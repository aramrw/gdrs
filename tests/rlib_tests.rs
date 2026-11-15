use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static RLIB_TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn gdrsc_bin() -> &'static str {
    env!("CARGO_BIN_EXE_gdrsc")
}

fn fresh_temp_dir(label: &str) -> PathBuf {
    let id = RLIB_TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = std::env::temp_dir().join(format!("gdrsc_rlib_test_{label}_{}_{id}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write_file(path: &Path, content: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, content).unwrap();
}

fn assert_cmd_ok(out: &Output, context: &str) {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "{context} failed (exit {:?})\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}",
        out.status.code()
    );
}

#[test]
fn gdrsc_transitive_three_crate_chain_and_out_of_order_extern() {
    let root = fresh_temp_dir("gdrsc_transitive");
    let build_dir = root.join("out");
    fs::create_dir_all(&build_dir).unwrap();

    let base_src = root.join("base/src/lib.gdrs");
    write_file(
        &base_src,
        "pub fn base_val() -> i64:\n    return 40\n",
    );

    let mid_src = root.join("mid/src/lib.gdrs");
    write_file(
        &mid_src,
        "use base::base_val\n\npub fn mid_val() -> i64:\n    return base_val() + 2\n",
    );

    let app_src = root.join("app/src/main.gdrs");
    write_file(
        &app_src,
        "use mid::mid_val\n\nfn main():\n    log!(\"ans={}\", mid_val())\n",
    );

    let base_rlib = build_dir.join("libbase.rlib");
    let mid_rlib = build_dir.join("libmid.rlib");
    let app_bin = build_dir.join("app_bin");

    // 1. Compile base
    let out = Command::new(gdrsc_bin())
        .args(["build"])
        .arg(&base_src)
        .args(["--crate-type", "lib", "--crate-name", "base", "-o"])
        .arg(&base_rlib)
        .output()
        .unwrap();
    assert_cmd_ok(&out, "gdrsc build base");
    assert!(base_rlib.exists(), "libbase.rlib not created");

    // 2. Compile mid referencing base
    let out = Command::new(gdrsc_bin())
        .args(["build"])
        .arg(&mid_src)
        .args([
            "--crate-type",
            "lib",
            "--crate-name",
            "mid",
            "--extern",
            &format!("base={}", base_rlib.display()),
            "-o",
        ])
        .arg(&mid_rlib)
        .output()
        .unwrap();
    assert_cmd_ok(&out, "gdrsc build mid");

    // 3. Compile app with `--extern` flags passed in reverse dependency order (`mid` before `base`)
    let out = Command::new(gdrsc_bin())
        .args(["build"])
        .arg(&app_src)
        .args([
            "--crate-type",
            "bin",
            "--crate-name",
            "app",
            "--extern",
            &format!("mid={}", mid_rlib.display()),
            "--extern",
            &format!("__trans_base={}", base_rlib.display()),
            "-o",
        ])
        .arg(&app_bin)
        .output()
        .unwrap();
    assert_cmd_ok(&out, "gdrsc build app with reversed extern order");

    let run_out = Command::new(&app_bin).output().unwrap();
    assert_cmd_ok(&run_out, "running app_bin");
    let stdout = String::from_utf8_lossy(&run_out.stdout);
    assert!(
        stdout.contains("ans=42"),
        "expected ans=42 in output, got:\n{stdout}"
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn gdrsc_custom_from_slice_and_underscore_t_method_export() {
    let root = fresh_temp_dir("from_slice_t_export");
    let build_dir = root.join("out");
    fs::create_dir_all(&build_dir).unwrap();

    let lib_src = root.join("mylib/src/lib.gdrs");
    write_file(
        &lib_src,
        "pub obj BoxVal:\n    pub val: i64\n\nimpl BoxVal:\n    pub fn from_slice(s: &[i64]) -> BoxVal:\n        return BoxVal{ val: s[0] + s[1] }\n\n    pub fn t(&self) -> i64:\n        return self.val * 2\n\npub fn helper_t_fn(x: i64) -> i64:\n    return x + 1\n",
    );

    let app_src = root.join("app/src/main.gdrs");
    write_file(
        &app_src,
        "use mylib::{BoxVal, helper_t_fn}\n\nfn main():\n    let bv = BoxVal::from_slice(&[10, 11])\n    log!(\"t={} helper={}\", bv.t(), helper_t_fn(5))\n",
    );

    let rlib = build_dir.join("libmylib.rlib");
    let app_bin = build_dir.join("app_bin");

    let lib_out = Command::new(gdrsc_bin())
        .args(["build"])
        .arg(&lib_src)
        .args(["--crate-type", "lib", "--crate-name", "mylib", "-o"])
        .arg(&rlib)
        .output()
        .unwrap();
    assert_cmd_ok(&lib_out, "gdrsc build mylib");

    let app_out = Command::new(gdrsc_bin())
        .args(["build"])
        .arg(&app_src)
        .args([
            "--crate-type",
            "bin",
            "--crate-name",
            "app",
            "--extern",
            &format!("mylib={}", rlib.display()),
            "-o",
        ])
        .arg(&app_bin)
        .output()
        .unwrap();
    assert_cmd_ok(&app_out, "gdrsc build app");

    let run_out = Command::new(&app_bin).output().unwrap();
    assert_cmd_ok(&run_out, "run app");
    let stdout = String::from_utf8_lossy(&run_out.stdout);
    assert!(stdout.contains("t=42 helper=6"), "stdout:\n{stdout}");

    let _ = fs::remove_dir_all(&root);
}
