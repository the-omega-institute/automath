from __future__ import annotations

import importlib
import sys
import traceback
from dataclasses import dataclass
from typing import Callable, List, Optional


@dataclass(frozen=True)
class Check:
    name: str
    module: str
    func: str = "run"


CHECKS: List[Check] = [
    Check(name="Sofic joint law (Sec.4.3)", module="verify_sofic_joint"),
    Check(name="Spectrum + CLT consistency (Sec.4.4-4.5)", module="verify_spectrum"),
    Check(name="Discriminants + fingerprint (Sec.6-7)", module="verify_discriminants"),
    Check(name="Worst-case family (Sec.4.2)", module="verify_worst_case"),
]


def _run_check(chk: Check) -> str:
    mod = importlib.import_module(chk.module)
    fn = getattr(mod, chk.func, None)
    if fn is None or not callable(fn):
        raise RuntimeError(f"模块 {chk.module} 缺少可调用函数 {chk.func}()")
    return str(fn())


def main(argv: Optional[list[str]] = None) -> int:
    _ = argv or sys.argv[1:]

    print("== 论文验证脚本：run_all ==")
    print(f"Python: {sys.version.split()[0]}")
    print()

    ok = 0
    failed = 0
    for chk in CHECKS:
        print(f"[RUN] {chk.name}")
        try:
            msg = _run_check(chk)
        except Exception:
            failed += 1
            print(f"[FAIL] {chk.name}")
            traceback.print_exc()
            print()
            continue
        ok += 1
        print(f"[OK] {msg}")
        print()

    print("== 汇总 ==")
    print(f"通过: {ok}")
    print(f"失败: {failed}")
    return 0 if failed == 0 else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

