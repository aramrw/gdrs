#![feature(type_alias_impl_trait)]

pub mod math;
pub mod stmt;

use crate::ast::*;
use chumsky::prelude::*;
use math::{math_parser};
use stmt::{stmt_parser};

// Types
// impl Parser<Token, Expr, Error = Simple<Token>> + Clone + 'a;

// ==========================================
// 4. PARSER (Chumsky)
// ==========================================
pub fn parser() -> impl Parser<Token, Program, Error = Simple<Token>> {
    let type_parser = recursive(|type_parser| {
        let array_type = just(Token::LBracket)
            .ignore_then(type_parser.clone())
            .then_ignore(just(Token::RBracket))
            .map(|t| Type::Vec(intern_type(t)));

        let generic_type = just(Token::Dollar)
            .ignore_then(select! { Token::Ident(s) => s })
            .map(|s| Type::Generic(intern_str(&s)));

        let dyn_type = just(Token::Dyn)
            .ignore_then(select! { Token::Ident(s) => s })
            .map(|s| Type::DynTrait(intern_str(&s)));

        let rc_type = just(Token::TypeRc)
            .ignore_then(just(Token::LBracket))
            .ignore_then(type_parser.clone())
            .then_ignore(just(Token::RBracket))
            .map(|t| Type::Rc(intern_type(t)));

        let arc_type = just(Token::TypeArc)
            .ignore_then(just(Token::LBracket))
            .ignore_then(type_parser.clone())
            .then_ignore(just(Token::RBracket))
            .map(|t| Type::Arc(intern_type(t)));

        let path_obj_type = select! { Token::Ident(s) => s }
            .separated_by(just(Token::ColonColon))
            .at_least(1)
            .then(
                type_parser
                    .clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LessThan), just(Token::GreaterThan))
                    .or_not(),
            )
            .map(|(parts, opt_generics)| {
                let name = parts.join("::");
                if (name == "Result" || name == "Option") && opt_generics.is_none() {
                    Type::Obj(intern_str(&format!("{}_bare", name)))
                } else {
                    Type::Obj(intern_str(&name))
                }
            });

        select! {
            Token::TypeI64 => Type::Int,
            Token::TypeI32 => Type::I32,
            Token::TypeFloat => Type::Float,
            Token::TypeF32 => Type::F32,
            Token::TypeBool => Type::Bool,
            Token::TypeStr => Type::Str,
            Token::TypeString => Type::String,
        }
        .or(path_obj_type)
        .or(generic_type)
        .or(dyn_type)
        .or(array_type)
        .or(rc_type)
        .or(arc_type)
    });

    // 3. Math Expression parser with operator precedence hierarchy
    let math = math_parser();

    // 4. Recursive statement and block parser
    let stmt = stmt_parser(math, type_parser.clone());

    let self_param = select! { Token::Ident(s) if s == "self" => s }
        .map_with_span(|s, span| Param { name: s, is_mutable: false, ty: Type::Unit, span });
    let mut_self_param = just(Token::Mut)
        .ignore_then(select! { Token::Ident(s) if s == "self" => s })
        .map_with_span(|s, span| Param { name: s, is_mutable: true, ty: Type::Unit, span });
    let param = mut_self_param.or(self_param).or(
        select! { Token::Ident(name) => name }
            .then_ignore(just(Token::Colon))
            .then(type_parser.clone())
            .map_with_span(|(name, ty), span| Param { name, is_mutable: false, ty, span }),
    );

    let where_clause = just(Token::Where)
        .ignore_then(just(Token::Dollar).or_not())
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::Colon))
        .then(
            select! { Token::Ident(s) => s }
                .separated_by(just(Token::Plus))
                .at_least(1),
        )
        .map_with_span(|(target_param, bounds), span| WhereClause {
            target_param,
            bounds,
            span,
        });

    let opt_where = just(Token::Newline)
        .repeated()
        .ignore_then(where_clause.clone())
        .or_not();

    // Function signature: fn name(params) -> return_type where T: Bounds:
    let function = just(Token::Fn)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.clone().separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser.clone()).or_not())
        .then(opt_where.clone())
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            stmt.repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(
            |((((name, params), opt_ret), where_clause), body), _| FuncDecl {
                name,
                params,
                return_type: opt_ret.unwrap_or(Type::Unit),
                where_clause,
                body,
            },
        );

    let func_sig = just(Token::Fn)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.clone().separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser.clone()).or_not())
        .then(opt_where.clone())
        .then_ignore(just(Token::Colon).or_not())
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|(((name, params), opt_ret), where_clause), _| FuncDecl {
            name,
            params,
            return_type: opt_ret.unwrap_or(Type::Unit),
            where_clause,
            body: Vec::new(),
        });

    let trait_method = function.clone().or(func_sig);

    let trait_decl = just(Token::Trait)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            trait_method
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(|(name, methods), span| TraitDecl {
            name,
            methods,
            span,
        });

    let trait_alias_decl = just(Token::TypeKw)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::Assign))
        .then(
            select! { Token::Ident(s) => s }
                .separated_by(just(Token::Plus))
                .at_least(1),
        )
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|(name, traits), span| TraitAliasDecl { name, traits, span });

    let attr_arg = select! { Token::Ident(s) => s }
        .or(select! { Token::String(s) => s });

    let attr_args = attr_arg
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .or_not()
        .map(|opt| opt.unwrap_or_default());

    let attribute = just(Token::Hash)
        .ignore_then(just(Token::LBracket))
        .ignore_then(select! { Token::Ident(s) => s })
        .then(attr_args)
        .then_ignore(just(Token::RBracket))
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|(name, args), span: Span| Attribute { name, args, span });

    let opt_attributes = attribute.repeated();

    let field_decl = opt_attributes
        .clone()
        .then(select! { Token::Ident(name) => name })
        .then_ignore(just(Token::Colon))
        .then(type_parser.clone())
        .map_with_span(|((attributes, name), ty), span| FieldDecl { name, ty, attributes, span })
        .then_ignore(just(Token::Newline).or_not());

    let obj_decl = opt_attributes
        .clone()
        .then_ignore(just(Token::Obj))
        .then(select! { Token::Ident(s) => s })
        .then(opt_where.clone())
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            field_decl
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(|(((attributes, name), where_clause), fields), span| StructDecl {
            name,
            fields,
            attributes,
            where_clause,
            span,
        });

    let enum_variant = opt_attributes
        .clone()
        .then(select! { Token::Ident(name) => name })
        .then(
            type_parser
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .or_not(),
        )
        .map_with_span(|((attributes, name), payload), span| EnumVariantDecl {
            name,
            payload_types: payload.unwrap_or_default(),
            attributes,
            span,
        })
        .then_ignore(just(Token::Newline).or_not());

    let enum_decl = opt_attributes
        .clone()
        .then_ignore(just(Token::Enum))
        .then(select! { Token::Ident(s) => s })
        .then(opt_where.clone())
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            enum_variant
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(|(((attributes, name), where_clause), variants), span| EnumDecl {
            name,
            variants,
            attributes,
            where_clause,
            span,
        });

    let impl_header = select! { Token::Ident(s) => s }
        .then(
            select! { Token::Ident(s) if s == "for" => s }
                .ignore_then(select! { Token::Ident(s) => s })
                .or_not(),
        )
        .map(|(first, opt_target)| match opt_target {
            Some(target) => (Some(first), target),
            None => (None, first),
        });

    let impl_decl = just(Token::Impl)
        .ignore_then(impl_header)
        .then(opt_where)
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            function
                .clone()
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(
            |(((trait_name, target_type), where_clause), methods), span| ImplDecl {
                trait_name,
                target_type,
                methods,
                where_clause,
                span,
            },
        );

    let path_parser = select! { Token::Ident(s) => s }
        .separated_by(just(Token::ColonColon))
        .at_least(1);

    let mod_decl = just(Token::Mod)
        .ignore_then(path_parser.clone())
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|path, span| ModDecl { path, span });

    let as_keyword = select! { Token::Ident(s) if s == "as" => s };

    let item_with_alias = select! { Token::Ident(s) => s }
        .then(as_keyword.clone().ignore_then(select! { Token::Ident(s) => s }).or_not());

    let multi_import_items = item_with_alias
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .delimited_by(just(Token::LBrace), just(Token::RBrace));

    let multi_use_path = path_parser
        .clone()
        .then_ignore(just(Token::ColonColon))
        .then(multi_import_items)
        .map(|(prefix_path, items)| {
            items
                .into_iter()
                .map(|(item, alias)| {
                    let mut p = prefix_path.clone();
                    p.push(item);
                    (p, alias)
                })
                .collect::<Vec<_>>()
        });

    let single_use_path = path_parser
        .clone()
        .then(as_keyword.ignore_then(select! { Token::Ident(s) => s }).or_not())
        .map(|(path, alias)| vec![(path, alias)]);

    let use_decl = just(Token::Use)
        .ignore_then(multi_use_path.or(single_use_path))
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|entries, span: Span| {
            Item::Uses(
                entries
                    .into_iter()
                    .map(|(path, alias)| UseDecl {
                        path,
                        alias,
                        span: span.clone(),
                    })
                    .collect(),
            )
        });

    let extern_fn_sig = just(Token::Fn)
        .ignore_then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.clone().separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser.clone()).or_not())
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|((name, params), opt_ret), span| ExternFnDecl {
            name,
            params,
            return_type: opt_ret.unwrap_or(Type::Unit),
            span,
        });

    let extern_decl = just(Token::Extern)
        .ignore_then(select! { Token::String(s) => s })
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).or_not())
        .then(
            extern_fn_sig
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        )
        .map_with_span(|(abi, functions), span| ExternDecl {
            abi,
            functions,
            span,
        });

    let item = just(Token::Newline)
        .repeated()
        .ignore_then(
            mod_decl
                .map(Item::Mod)
                .or(use_decl)
                .or(trait_decl.map(Item::Trait))
                .or(trait_alias_decl.map(Item::TraitAlias))
                .or(extern_decl.map(Item::Extern))
                .or(function.map(Item::Func))
                .or(obj_decl.map(Item::Struct))
                .or(enum_decl.map(Item::Enum))
                .or(impl_decl.map(Item::Impl)),
        )
        .then_ignore(just(Token::Newline).repeated());

    item.repeated().then_ignore(end()).map(|items| {
        let mut mods = Vec::new();
        let mut uses = Vec::new();
        let mut traits = Vec::new();
        let mut trait_aliases = Vec::new();
        let mut externs = Vec::new();
        let mut structs = Vec::new();
        let mut enums = Vec::new();
        let mut impls = Vec::new();
        let mut functions = Vec::new();
        for item in items {
            match item {
                Item::Mod(m) => mods.push(m),
                Item::Uses(u_list) => uses.extend(u_list),
                Item::Trait(t) => traits.push(t),
                Item::TraitAlias(ta) => trait_aliases.push(ta),
                Item::Extern(ext) => externs.push(ext),
                Item::Func(f) => functions.push(f),
                Item::Struct(s) => structs.push(s),
                Item::Enum(e) => enums.push(e),
                Item::Impl(i) => impls.push(i),
            }
        }
        Program {
            mods,
            uses,
            traits,
            trait_aliases,
            externs,
            structs,
            enums,
            impls,
            functions,
        }
    })
}

enum Item {
    Mod(ModDecl),
    Uses(Vec<UseDecl>),
    Trait(TraitDecl),
    TraitAlias(TraitAliasDecl),
    Extern(ExternDecl),
    Func(FuncDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
    Impl(ImplDecl),
}
