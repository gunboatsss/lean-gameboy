import Lake
open Lake DSL System

package lean_gameboy where
  version := v!"0.1.0"

lean_lib LeanGameboy where
  roots := #[`LeanGameboy]

-- SDL shim as a native static lib. SDL2 itself is dlopen'd at runtime,
-- so the build only needs a C compiler and lean headers (no SDL dev
-- packages, no link-time -lSDL2).
target libgbsdl pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "shim.o"
  let srcJob ← inputFile (pkg.dir / "c" / "shim.c") true
  let includeDir := (← getLeanIncludeDir).toString
  let oJob ← buildO oFile srcJob #["-I", includeDir, "-fPIC"]
  let libFile := pkg.buildDir / "c" / nameToStaticLib "gbsdl"
  buildStaticLib libFile #[oJob]

@[default_target]
lean_exe «lean-gameboy» where
  root := `Main
  moreLinkArgs := #["-ldl"]
  moreLinkObjs := #[libgbsdl]

lean_exe «gb-test» where
  root := `Tests.Smoke

lean_exe «gb-bench» where
  root := `Tests.Bench
  moreLinkArgs := #["-ldl"]
  moreLinkObjs := #[libgbsdl]
