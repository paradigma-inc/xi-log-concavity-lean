import json
import re
import secrets
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from tproof.layout import Paths


def now_utc_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _sanitize_label(label: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9_-]+", "-", label.strip()).strip("-")
    return cleaned[:40] if cleaned else "run"


def new_run_id(label: str | None = None) -> str:
    prefix = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    token = secrets.token_hex(2)
    if label:
        return f"{prefix}_{_sanitize_label(label)}_{token}"
    return f"{prefix}_{token}"


def run_dir(paths: Paths, run_id: str) -> Path:
    return paths.runs_dir / run_id


def run_file(paths: Paths, run_id: str) -> Path:
    return run_dir(paths, run_id) / "run.json"


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def create_run(paths: Paths, run_id: str, payload: dict[str, Any]) -> None:
    run_dir(paths, run_id).mkdir(parents=True, exist_ok=True)
    write_json(run_file(paths, run_id), payload)


def load_run(paths: Paths, run_id: str) -> dict[str, Any]:
    path = run_file(paths, run_id)
    if not path.is_file():
        raise FileNotFoundError(f"Unknown run id '{run_id}'. Missing file: {path}")
    return read_json(path)


def save_run(paths: Paths, run_id: str, payload: dict[str, Any]) -> None:
    write_json(run_file(paths, run_id), payload)
