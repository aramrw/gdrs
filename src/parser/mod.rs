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
pub fn parser() -> BoxedParser<'static, Token, Program, Simple<Token>> {
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

        let tuple_or_unit_type = just(Token::LParen)
            .ignore_then(
                type_parser
                    .clone()
                    .then(
                        just(Token::Comma)
                            .ignore_then(
                                type_parser
                                    .clone()
                                    .separated_by(just(Token::Comma))
                                    .allow_trailing(),
                            )
                            .or_not(),
                    )
                    .or_not(),
            )
            .then_ignore(just(Token::RParen))
            .map(|opt| match opt {
                None => Type::Unit,
                Some((first, None)) => first,
                Some((first, Some(rest))) => {
                    let mut elems = Vec::with_capacity(1 + rest.len());
                    elems.push(first);
                    elems.extend(rest);
                    Type::Tuple(intern_tuple(&elems))
                }
            });

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
                let base_name = parts.join("::");
                let normalized_base = match base_name.as_str() {
                    "Opt" | "Option" => "std_core_Option".to_string(),
                    "Res" | "Result" => "std_core_Result".to_string(),
                    _ => base_name.replace("::", "_"),
                };
                if let Some(generics) = opt_generics {
                    if (normalized_base == "Vec" || normalized_base == "std_vec_Vec") && generics.len() == 1 {
                        return Type::Vec(intern_type(generics[0]));
                    }
                    let mangled = crate::sanal::mono::mangle_name(&normalized_base, &generics);
                    Type::Obj(intern_str(&mangled))
                } else if normalized_base == "std_core_Result" || normalized_base == "std_core_Option" {
                    Type::Obj(intern_str(&format!("{}_bare", normalized_base)))
                } else {
                    Type::Obj(intern_str(&normalized_base))
                }
            });

        let ref_type = just(Token::Ampersand)
            .ignore_then(just(Token::Mut).or_not())
            .then(type_parser.clone())
            .map(|(opt_mut, inner_ty)| {
                if opt_mut.is_some() {
                    Type::MutRef(intern_type(inner_ty))
                } else {
                    Type::Ref(intern_type(inner_ty))
                }
            });

        let ptr_type = just(Token::Star)
            .ignore_then(type_parser.clone())
            .map(|inner_ty| Type::Ptr(intern_type(inner_ty)));

        select! {
            Token::TypeI64 => Type::Int,
            Token::TypeI32 => Type::I32,
            Token::TypeI16 => Type::I16,
            Token::TypeI8 => Type::I8,
            Token::TypeU64 => Type::U64,
            Token::TypeU32 => Type::U32,
            Token::TypeU16 => Type::U16,
            Token::TypeU8 => Type::U8,
            Token::TypeUsize => Type::U64,
            Token::TypeIsize => Type::Int,
            Token::TypeFloat => Type::Float,
            Token::TypeF32 => Type::F32,
            Token::TypeBool => Type::Bool,
            Token::TypeStr => Type::Str,
            Token::TypeString => Type::String,
            Token::TypeVoid => Type::Void,
        }
        .or(ptr_type)
        .or(ref_type)
        .or(path_obj_type)
        .or(generic_type)
        .or(dyn_type)
        .or(array_type)
        .or(rc_type)
        .or(arc_type)
        .or(tuple_or_unit_type)
    }).boxed();

    // 3. Math Expression parser with operator precedence hierarchy
    let math = math_parser(type_parser.clone());

    // 4. Recursive statement and block parser
    let stmt = stmt_parser(math, type_parser.clone());

    let ref_mut_self_param = just(Token::Ampersand)
        .ignore_then(just(Token::Mut))
        .ignore_then(select! { Token::Ident(s) if s == "self" => s })
        .map_with_span(|s, span| Param { name: s, is_mutable: true, ty: Type::MutRef(intern_type(Type::Unit)), span });
    let ref_self_param = just(Token::Ampersand)
        .ignore_then(select! { Token::Ident(s) if s == "self" => s })
        .map_with_span(|s, span| Param { name: s, is_mutable: false, ty: Type::Ref(intern_type(Type::Unit)), span });
    let mut_self_param = just(Token::Mut)
        .ignore_then(select! { Token::Ident(s) if s == "self" => s })
        .map_with_span(|s, span| Param { name: s, is_mutable: true, ty: Type::Unit, span });
    let self_param = select! { Token::Ident(s) if s == "self" => s }
        .map_with_span(|s, span| Param { name: s, is_mutable: false, ty: Type::Unit, span });

    let param = ref_mut_self_param
        .or(ref_self_param)
        .or(mut_self_param)
        .or(self_param)
        .or(
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

    let layout_junk = just(Token::Newline)
        .or(just(Token::Indent))
        .or(just(Token::Dedent))
        .repeated();

    let colon_fn_body = just(Token::Colon)
        .then_ignore(just(Token::Newline).or_not())
        .ignore_then(
            stmt.clone()
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        );

    let braced_fn_body = just(Token::Newline)
        .repeated()
        .ignore_then(just(Token::LBrace))
        .ignore_then(layout_junk.clone())
        .ignore_then(stmt.padded_by(layout_junk.clone()).repeated())
        .then_ignore(layout_junk.clone())
        .then_ignore(just(Token::RBrace));

    let fn_body = colon_fn_body.or(braced_fn_body);

    let opt_vis = just(Token::Pub)
        .ignore_then(
            just(Token::Crate)
                .to(Visibility::PubCrate)
                .or(just(Token::Super).to(Visibility::PubSuper))
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .or_not(),
        )
        .map(|inner| inner.unwrap_or(Visibility::Pub))
        .or_not()
        .map(|opt| opt.unwrap_or(Visibility::Private));

    // Function signature: #[track_caller] pub fn name(params) -> return_type where T: Bounds:
    let function = opt_attributes
        .clone()
        .then(opt_vis.clone())
        .then_ignore(just(Token::Fn))
        .then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.clone().separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser.clone()).or_not())
        .then(opt_where.clone())
        .then(fn_body)
        .map_with_span(
            |((((((attributes, vis), name), params), opt_ret), where_clause), body), _| FuncDecl {
                name,
                params,
                return_type: opt_ret.unwrap_or(Type::Unit),
                where_clause,
                body,
                is_track_caller: attributes.iter().any(|a| a.name == "track_caller"),
                vis,
                module_path: Vec::new(),
                is_trait_impl: false,
            },
        )
        .boxed();

    let func_sig = opt_attributes
        .clone()
        .then_ignore(just(Token::Fn))
        .then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.clone().separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser.clone()).or_not())
        .then(opt_where.clone())
        .then_ignore(just(Token::Colon).or(just(Token::Semicolon)).or_not())
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|((((attributes, name), params), opt_ret), where_clause), _| FuncDecl {
            name,
            params,
            return_type: opt_ret.unwrap_or(Type::Unit),
            where_clause,
            body: Vec::new(),
            is_track_caller: attributes.iter().any(|a| a.name == "track_caller"),
            vis: Visibility::Pub,
            module_path: Vec::new(),
            is_trait_impl: false,
        });

    let trait_method = function.clone().or(func_sig);

    let colon_trait_methods = just(Token::Colon)
        .then_ignore(just(Token::Newline).or_not())
        .ignore_then(
            trait_method
                .clone()
                .padded_by(just(Token::Newline).repeated())
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        );

    let braced_trait_methods = just(Token::Newline)
        .repeated()
        .ignore_then(just(Token::LBrace))
        .ignore_then(layout_junk.clone())
        .ignore_then(trait_method.padded_by(layout_junk.clone()).repeated())
        .then_ignore(layout_junk.clone())
        .then_ignore(just(Token::RBrace));

    let trait_methods = colon_trait_methods.or(braced_trait_methods);

    let trait_decl = opt_vis
        .clone()
        .then_ignore(just(Token::Trait))
        .then(select! { Token::Ident(s) => s })
        .then(trait_methods)
        .map_with_span(|((vis, name), methods), span| TraitDecl {
            name,
            methods,
            vis,
            module_path: Vec::new(),
            span,
        })
        .boxed();

    let trait_alias_decl = opt_vis
        .clone()
        .then_ignore(just(Token::TypeKw))
        .then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::Assign))
        .then(
            select! { Token::Ident(s) => s }
                .separated_by(just(Token::Plus))
                .at_least(1),
        )
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|((vis, name), traits), span| TraitAliasDecl {
            name,
            traits,
            vis,
            module_path: Vec::new(),
            span,
        });

    let field_decl = opt_attributes
        .clone()
        .then(opt_vis.clone())
        .then(select! { Token::Ident(name) => name })
        .then_ignore(just(Token::Colon))
        .then(type_parser.clone())
        .map_with_span(|(((attributes, vis), name), ty), span| FieldDecl {
            name,
            ty,
            vis,
            attributes,
            span,
        })
        .then_ignore(just(Token::Comma).or_not())
        .then_ignore(just(Token::Newline).or_not());

    let colon_obj_fields = just(Token::Colon)
        .then_ignore(just(Token::Newline).or_not())
        .ignore_then(
            field_decl
                .clone()
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        );

    let braced_obj_fields = just(Token::Newline)
        .repeated()
        .ignore_then(just(Token::LBrace))
        .ignore_then(layout_junk.clone())
        .ignore_then(field_decl.padded_by(layout_junk.clone()).repeated())
        .then_ignore(layout_junk.clone())
        .then_ignore(just(Token::RBrace));

    let obj_fields = colon_obj_fields.or(braced_obj_fields);

    let obj_decl = opt_attributes
        .clone()
        .then(opt_vis.clone())
        .then_ignore(just(Token::Obj))
        .then(select! { Token::Ident(s) => s })
        .then(opt_where.clone())
        .then(obj_fields)
        .map_with_span(|((((attributes, vis), name), where_clause), fields), span| StructDecl {
            name,
            fields,
            vis,
            module_path: Vec::new(),
            attributes,
            where_clause,
            span,
        })
        .boxed();

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
        .then_ignore(just(Token::Comma).or_not())
        .then_ignore(just(Token::Newline).or_not());

    let colon_enum_variants = just(Token::Colon)
        .then_ignore(just(Token::Newline).or_not())
        .ignore_then(
            enum_variant
                .clone()
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        );

    let braced_enum_variants = just(Token::Newline)
        .repeated()
        .ignore_then(just(Token::LBrace))
        .ignore_then(layout_junk.clone())
        .ignore_then(enum_variant.padded_by(layout_junk.clone()).repeated())
        .then_ignore(layout_junk.clone())
        .then_ignore(just(Token::RBrace));

    let enum_variants = colon_enum_variants.or(braced_enum_variants);

    let enum_decl = opt_attributes
        .clone()
        .then(opt_vis.clone())
        .then_ignore(just(Token::Enum))
        .then(select! { Token::Ident(s) => s })
        .then(opt_where.clone())
        .then(enum_variants)
        .map_with_span(|((((attributes, vis), name), where_clause), variants), span| EnumDecl {
            name,
            variants,
            vis,
            module_path: Vec::new(),
            attributes,
            where_clause,
            span,
        })
        .boxed();

    let impl_header = select! { Token::Ident(s) => s }
        .then(
            just(Token::For)
                .map(|_| "for".to_string())
                .or(select! { Token::Ident(s) if s == "for" => s })
                .ignore_then(select! { Token::Ident(s) => s })
                .or_not(),
        )
        .map(|(first, opt_target)| match opt_target {
            Some(target) => (Some(first), target),
            None => (None, first),
        });

    let colon_impl_methods = just(Token::Colon)
        .then_ignore(just(Token::Newline).or_not())
        .ignore_then(
            function
                .clone()
                .padded_by(just(Token::Newline).repeated())
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        );

    let braced_impl_methods = just(Token::Newline)
        .repeated()
        .ignore_then(just(Token::LBrace))
        .ignore_then(layout_junk.clone())
        .ignore_then(function.clone().padded_by(layout_junk.clone()).repeated())
        .then_ignore(layout_junk.clone())
        .then_ignore(just(Token::RBrace));

    let impl_methods = colon_impl_methods.or(braced_impl_methods);

    let impl_decl = just(Token::Impl)
        .ignore_then(impl_header)
        .then(opt_where)
        .then(impl_methods)
        .map_with_span(
            |(((trait_name, target_type), where_clause), methods), span| ImplDecl {
                trait_name,
                target_type,
                methods,
                where_clause,
                span,
            },
        )
        .boxed();

    let any_ident = select! {
        Token::Ident(s) => s,
        Token::TypeString => "string".to_string(),
        Token::TypeStr => "str".to_string(),
    };

    let path_parser = any_ident
        .clone()
        .separated_by(just(Token::ColonColon))
        .at_least(1);

    let mod_decl = just(Token::Mod)
        .ignore_then(path_parser.clone())
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|path, span| ModDecl { path, span });

    let as_keyword = just(Token::As)
        .to("as".to_string())
        .or(select! { Token::Ident(s) if s == "as" => s });

    let item_with_alias = any_ident
        .clone()
        .then(as_keyword.clone().ignore_then(any_ident.clone()).or_not());


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

    let use_decl = opt_vis
        .clone()
        .then_ignore(just(Token::Use))
        .then(multi_use_path.or(single_use_path))
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|(vis, entries), span: Span| {
            Item::Uses(
                entries
                    .into_iter()
                    .map(|(path, alias)| UseDecl {
                        path,
                        alias,
                        vis,
                        module_path: Vec::new(),
                        resolved_target: String::new(),
                        span: span.clone(),
                    })
                    .collect(),
            )
        })
        .boxed();

    let extern_fn_sig = opt_vis
        .clone()
        .then_ignore(just(Token::Fn))
        .then(select! { Token::Ident(s) => s })
        .then_ignore(just(Token::LParen))
        .then(param.clone().separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser.clone()).or_not())
        .then_ignore(just(Token::Newline).or_not())
        .map_with_span(|(((vis, name), params), opt_ret), span| ExternFnDecl {
            c_name: name.clone(),
            name,
            params,
            return_type: opt_ret.unwrap_or(Type::Unit),
            vis,
            module_path: Vec::new(),
            span,
        });

    let colon_extern_funcs = just(Token::Colon)
        .then_ignore(just(Token::Newline).or_not())
        .ignore_then(
            extern_fn_sig
                .clone()
                .padded_by(just(Token::Newline).repeated())
                .repeated()
                .at_least(1)
                .delimited_by(just(Token::Indent), just(Token::Dedent)),
        );

    let braced_extern_funcs = just(Token::Newline)
        .repeated()
        .ignore_then(just(Token::LBrace))
        .ignore_then(layout_junk.clone())
        .ignore_then(extern_fn_sig.padded_by(layout_junk.clone()).repeated())
        .then_ignore(layout_junk.clone())
        .then_ignore(just(Token::RBrace));

    let extern_funcs = colon_extern_funcs.or(braced_extern_funcs);

    let extern_decl = just(Token::Extern)
        .ignore_then(select! { Token::String(s) => s })
        .then(extern_funcs)
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
        .then_ignore(just(Token::Newline).repeated())
        .boxed();

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
    .boxed()
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
