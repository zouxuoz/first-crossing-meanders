#!/usr/bin/env python3
"""Regression cases for the source boundaries enforced by check_imports.py."""
import unittest

from check_imports import check_source


class ImportPolicyTests(unittest.TestCase):
    def test_library_cannot_import_root(self):
        for source in ["import Meanders\n", "import\n Meanders\n"]:
            with self.subTest(source=source):
                errors = check_source("Meanders/Core/Example.lean", source)
                self.assertTrue(any("imports an umbrella" in error for error in errors))

    def test_umbrellas_cannot_declare(self):
        for path in ["Meanders.lean", "Meanders/Core.lean"]:
            with self.subTest(path=path):
                errors = check_source(path, "def hidden : Nat := 0\n")
                self.assertTrue(any("other than import" in error for error in errors))

    def test_documented_umbrellas(self):
        source = "/-! Documentation /- nested comment -/ continues. -/\n"
        source += "-- import Meanders.Certify.Bad\nimport Meanders.Core.Arch -- leaf\n"
        self.assertEqual(check_source("Meanders/Core.lean", source), [])
        self.assertEqual(check_source("Meanders.lean", "import Meanders.Core Meanders.Models\n"), [])
        self.assertEqual(check_source("Meanders.lean", "import\n Meanders.Core\n"), [])

    def test_umbrella_import_boundaries(self):
        for path, imported in [("Meanders.lean", "Meanders"),
                               ("Meanders.lean", "Meanders.Core.Arch"),
                               ("Meanders/Core.lean", "Meanders.Models.Folded.State")]:
            with self.subTest(path=path, imported=imported):
                self.assertTrue(check_source(path, f"import {imported}\n"))

    def test_tests_and_executables_can_import_root(self):
        for path in ["MeandersTests.lean", "MeandersTests/Example.lean",
                     "Verify.lean", "ExportTheorem.lean"]:
            with self.subTest(path=path):
                self.assertEqual(check_source(path, "import Meanders\n"), [])

    def test_topic_modules_can_declare(self):
        self.assertEqual(check_source("Meanders/Core/Word.lean", "def example : Nat := 0\n"), [])

    def test_comments_and_strings_do_not_create_imports(self):
        source = '/- import Meanders /- nested -/ -/\n'
        source += 'def text := "\nimport Meanders\n/- not a comment -/"\n'
        self.assertEqual(check_source("Meanders/Core/Example.lean", source), [])

    def test_existing_layer_and_algorithm_boundaries(self):
        for source, target in [("Core.Example", "Models.Folded.State"),
                               ("Algorithms.Fused", "Algorithms.Folded")]:
            with self.subTest(source=source):
                path = "Meanders/" + source.replace(".", "/") + ".lean"
                self.assertTrue(check_source(path, f"import Meanders.{target}\n"))
        self.assertTrue(check_source("Meanders/Core/Example.lean", "import MeandersTests\n"))


if __name__ == "__main__":
    unittest.main()
