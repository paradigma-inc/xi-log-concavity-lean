import shutil
import subprocess
from pathlib import Path

from tproof.constants import PACKAGE_NAME


def run_cmd(command: list[str], cwd: Path) -> tuple[int, str]:
    proc = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
    )
    output = (proc.stdout or "") + (proc.stderr or "")
    return proc.returncode, output


def ensure_toolchain_installed(toolchain: str) -> tuple[int, str]:
    return run_cmd(["elan", "toolchain", "install", toolchain], cwd=Path.cwd())


def lake_update(project_dir: Path) -> tuple[int, str]:
    return run_cmd(["lake", "update"], cwd=project_dir)


def lake_build(project_dir: Path) -> tuple[int, str]:
    return run_cmd(["lake", "build"], cwd=project_dir)


def seed_lean_project(project_dir: Path, lean_toolchain: str, mathlib_hash: str) -> None:
    project_dir.mkdir(parents=True, exist_ok=True)
    package_dir = project_dir / PACKAGE_NAME
    package_dir.mkdir(parents=True, exist_ok=True)
    (package_dir / "Demo").mkdir(parents=True, exist_ok=True)
    (package_dir / "Final").mkdir(parents=True, exist_ok=True)
    (project_dir / "lean-toolchain").write_text(f"{lean_toolchain}\n", encoding="utf-8")
    (project_dir / "lakefile.lean").write_text(
        f"""import Lake
open Lake DSL

package "{PACKAGE_NAME}"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "{mathlib_hash}"

@[default_target]
lean_lib "{PACKAGE_NAME}" where
""",
        encoding="utf-8",
    )
    (project_dir / f"{PACKAGE_NAME}.lean").write_text(
        f"""import {PACKAGE_NAME}.AllProofs
""",
        encoding="utf-8",
    )
    all_proofs = project_dir / PACKAGE_NAME / "AllProofs.lean"
    if not all_proofs.is_file():
        all_proofs.write_text(
            """/-
Auto-generated import index for proof modules.
Regenerate with: tproof reindex
-/
""",
            encoding="utf-8",
        )

    placeholder = project_dir / PACKAGE_NAME / "Demo" / "Placeholder.lean"
    if not placeholder.is_file():
        placeholder.write_text(
            f"""namespace {PACKAGE_NAME}.Demo

theorem placeholder : True := by
  trivial

end {PACKAGE_NAME}.Demo
""",
            encoding="utf-8",
        )


def reindex_allproofs(project_dir: Path) -> Path:
    package_dir = project_dir / PACKAGE_NAME
    modules: list[str] = []
    if package_dir.is_dir():
        for lean_file in sorted(package_dir.rglob("*.lean")):
            rel = lean_file.relative_to(project_dir).with_suffix("")
            module_name = ".".join(rel.parts)
            if module_name.endswith(".AllProofs"):
                continue
            modules.append(module_name)

    all_proofs_path = package_dir / "AllProofs.lean"
    lines = [
        "/-",
        "Auto-generated import index for proof modules.",
        "Regenerate with: tproof reindex",
        "-/",
        "",
    ]
    for module in modules:
        lines.append(f"import {module}")
    lines.append("")
    all_proofs_path.write_text("\n".join(lines), encoding="utf-8")
    return all_proofs_path


def snapshot_project(source_project_dir: Path, destination_dir: Path) -> None:
    if destination_dir.exists():
        shutil.rmtree(destination_dir)
    shutil.copytree(
        source_project_dir,
        destination_dir,
        ignore=shutil.ignore_patterns(".lake", "build", "__pycache__", "*.olean", "*.ilean"),
    )
