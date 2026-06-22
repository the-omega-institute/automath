import unittest
from unittest import mock

from tools.distillation import distill


class CliDiscoveryTests(unittest.TestCase):
    def test_find_codex_ignores_inaccessible_windows_fallback(self):
        with (
            mock.patch.object(distill.shutil, "which", return_value=None),
            mock.patch.object(distill.sys, "platform", "win32"),
            mock.patch.object(
                distill.Path,
                "exists",
                side_effect=PermissionError("access denied"),
            ),
        ):
            self.assertEqual(distill._find_codex(), "codex")

    def test_find_codex_ignores_non_executable_windows_fallback(self):
        with (
            mock.patch.object(distill.shutil, "which", return_value=None),
            mock.patch.object(distill.sys, "platform", "win32"),
            mock.patch.object(distill.Path, "exists", return_value=True),
            mock.patch.object(distill.os, "access", return_value=False),
        ):
            self.assertEqual(distill._find_codex(), "codex")

    def test_find_claude_ignores_inaccessible_windows_fallback(self):
        with (
            mock.patch.object(distill.shutil, "which", return_value=None),
            mock.patch.object(distill.sys, "platform", "win32"),
            mock.patch.object(
                distill.Path,
                "exists",
                side_effect=PermissionError("access denied"),
            ),
        ):
            self.assertEqual(distill._find_claude(), "claude")

    def test_find_claude_ignores_non_executable_windows_fallback(self):
        with (
            mock.patch.object(distill.shutil, "which", return_value=None),
            mock.patch.object(distill.sys, "platform", "win32"),
            mock.patch.object(distill.Path, "exists", return_value=True),
            mock.patch.object(distill.os, "access", return_value=False),
        ):
            self.assertEqual(distill._find_claude(), "claude")
