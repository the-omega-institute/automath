import tempfile
import unittest
from pathlib import Path

from tools.distillation import distill


class WritebackHygieneTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.old_core_body = distill.CORE_BODY
        self.core_body = Path(self.tmp.name) / "body"
        self.core_body.mkdir()
        distill.CORE_BODY = self.core_body
        (self.core_body / "target.tex").write_text(
            "\\section{局部结构}\n既有正文。\n",
            encoding="utf-8",
        )

    def tearDown(self):
        distill.CORE_BODY = self.old_core_body
        self.tmp.cleanup()

    def _validate(self, content: str):
        return distill._validate_writebacks(
            [
                {
                    "section": "局部结构",
                    "tex_file": "target.tex",
                    "type": "lemma",
                    "label": "lem:distill-hygiene",
                    "content": content,
                }
            ],
            allowed_tex_files={"target.tex"},
        )

    def test_accepts_chinese_body_claim_without_new_sectioning(self):
        content = r"""
\begin{lemma}[稳定限制的局部闭合]
\label{lem:distill-hygiene}
设 $\mathcal F$ 为目标节中已经给定的有限证书族。若每个证书在同一规范下相容，
则其限制后的读出仍保持相同的相容关系。
\end{lemma}
\begin{proof}
相容性在同一规范下逐项验证。限制操作只删除未被目标节调用的坐标，不改变已经
比较过的读出分量，故所有相等关系在限制后仍成立。
\end{proof}
""".strip()

        _, errors = self._validate(content)

        self.assertEqual(errors, [])

    def test_rejects_english_only_main_paper_content(self):
        content = r"""
\begin{lemma}[Stable restriction]
\label{lem:distill-hygiene}
Let $\mathcal F$ be a finite certificate family. Compatible certificates remain compatible after restriction.
\end{lemma}
\begin{proof}
The assertion follows by checking every coordinate.
\end{proof}
""".strip()

        _, errors = self._validate(content)

        self.assertTrue(
            any("Chinese main-paper academic prose" in error for error in errors),
            errors,
        )

    def test_rejects_sectioning_inside_writeback_snippet(self):
        content = r"""
\subsection{局部闭合}
\begin{lemma}[稳定限制]
\label{lem:distill-hygiene}
相容证书在限制后仍相容。
\end{lemma}
\begin{proof}
逐项限制即可。
\end{proof}
""".strip()

        _, errors = self._validate(content)

        self.assertTrue(
            any("opens a sectioning command" in error for error in errors),
            errors,
        )

    def test_rejects_visible_patch_style_language(self):
        content = r"""
\begin{lemma}[补充 A]
\label{lem:distill-hygiene}
相容证书在限制后仍相容。
\end{lemma}
\begin{proof}
逐项限制即可。
\end{proof}
""".strip()

        _, errors = self._validate(content)

        self.assertTrue(
            any("killo-golden" in error for error in errors),
            errors,
        )

    def test_rejects_manual_conclusion_ordinal(self):
        content = r"""
\begin{lemma}[结论 1: 稳定限制]
\label{lem:distill-hygiene}
相容证书在限制后仍相容。
\end{lemma}
\begin{proof}
逐项限制即可。
\end{proof}
""".strip()

        _, errors = self._validate(content)

        self.assertTrue(
            any("killo-golden" in error for error in errors),
            errors,
        )

    def test_accepts_mathematical_conclusion_phrase(self):
        content = r"""
\begin{lemma}[局部闭合的逆否形式]
\label{lem:distill-hygiene}
若限制后的读出不相容，则原证书族不可能在同一规范下相容。
\end{lemma}
\begin{proof}
这是前一结论的逆否命题：限制保持相容关系，故限制层的不相容性排除
原层相容性。该论证只使用目标节已经固定的限制映射。
\end{proof}
""".strip()

        _, errors = self._validate(content)

        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
