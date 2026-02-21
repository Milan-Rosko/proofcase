#!/usr/bin/env python3
"""
Independent Reference Implementation: Hilbert Proof Checker

This simple Python implementation validates the core proof checking logic
independently of the extracted OCaml code.

Hilbert proof system (implicational fragment):
  - Axiom K: A → (B → A)
  - Axiom S: (A → (B → C)) → ((A → B) → (A → C))
  - Axiom EFQ: ⊥ → A
  - Rule: Modus Ponens
"""

from dataclasses import dataclass
from typing import List, Union


# Formula representation
@dataclass
class Bot:
    """Bottom (falsum) ⊥"""
    def __eq__(self, other):
        return isinstance(other, Bot)

    def __hash__(self):
        return hash("Bot")

    def __str__(self):
        return "⊥"


@dataclass
class Imp:
    """Implication A → B"""
    left: 'Formula'
    right: 'Formula'

    def __eq__(self, other):
        return (isinstance(other, Imp) and
                self.left == other.left and
                self.right == other.right)

    def __hash__(self):
        return hash(("Imp", self.left, self.right))

    def __str__(self):
        left_str = str(self.left)
        right_str = str(self.right)
        if isinstance(self.left, Imp):
            left_str = f"({left_str})"
        return f"{left_str} → {right_str}"


Formula = Union[Bot, Imp]


# Axiom checkers
def is_K(formula: Formula) -> bool:
    """Check if formula matches K axiom: A → (B → A)"""
    if not isinstance(formula, Imp):
        return False
    if not isinstance(formula.right, Imp):
        return False
    return formula.left == formula.right.right


def is_S(formula: Formula) -> bool:
    """Check if formula matches S axiom: (A → (B → C)) → ((A → B) → (A → C))"""
    if not isinstance(formula, Imp):
        return False

    left = formula.left
    if not isinstance(left, Imp) or not isinstance(left.right, Imp):
        return False

    A = left.left
    B = left.right.left
    C = left.right.right

    right = formula.right
    if not isinstance(right, Imp) or not isinstance(right.left, Imp) or not isinstance(right.right, Imp):
        return False

    A_prime = right.left.left
    B_prime = right.left.right
    A_double_prime = right.right.left
    C_prime = right.right.right

    return (A == A_prime == A_double_prime and
            B == B_prime and
            C == C_prime)


def is_EFQ(formula: Formula) -> bool:
    """Check if formula matches EFQ axiom: ⊥ → A"""
    if not isinstance(formula, Imp):
        return False
    return isinstance(formula.left, Bot)


def is_axiom(formula: Formula) -> bool:
    """Check if formula is any axiom"""
    return is_K(formula) or is_S(formula) or is_EFQ(formula)


# Proof checking
def has_mp_witness(context: List[Formula], target: Formula) -> bool:
    """
    Check if target can be derived via Modus Ponens from context.
    MP rule: If we have φ and φ → ψ in context, we can derive ψ.
    """
    for phi in context:
        for chi in context:
            if isinstance(chi, Imp) and chi.left == phi and chi.right == target:
                return True
    return False


def check_proof(lines: List[Formula]) -> bool:
    """
    Check if a proof is valid.
    Each line must be either an axiom or derivable via MP from previous lines.
    """
    context = []
    for line in lines:
        if not (is_axiom(line) or has_mp_witness(context, line)):
            return False
        context.append(line)
    return True


def proves(proof: List[Formula], target: Formula) -> bool:
    """
    Check if proof is valid and proves target.
    Returns True iff proof is valid and last line equals target.
    """
    if not proof:
        return False
    if not check_proof(proof):
        return False
    return proof[-1] == target


# Test cases
def run_tests():
    print("═" * 60)
    print("  Independent Reference: Hilbert Proof Checker")
    print("═" * 60)
    print()

    tests_passed = 0
    tests_failed = 0

    # Test 1: K axiom recognition
    A = Bot()
    B = Imp(Bot(), Bot())
    k_axiom = Imp(A, Imp(B, A))

    print("Test 1: K axiom recognition")
    print(f"  Formula: {k_axiom}")
    if is_K(k_axiom):
        print("  ✓ PASS")
        tests_passed += 1
    else:
        print("  ✗ FAIL")
        tests_failed += 1
    print()

    # Test 2: EFQ axiom recognition
    efq = Imp(Bot(), Bot())
    print("Test 2: EFQ axiom recognition")
    print(f"  Formula: {efq}")
    if is_EFQ(efq):
        print("  ✓ PASS")
        tests_passed += 1
    else:
        print("  ✗ FAIL")
        tests_failed += 1
    print()

    # Test 3: Single axiom proves itself
    proof1 = [k_axiom]
    print("Test 3: K axiom proves itself")
    print(f"  Proof: [{k_axiom}]")
    print(f"  Target: {k_axiom}")
    if proves(proof1, k_axiom):
        print("  ✓ PASS")
        tests_passed += 1
    else:
        print("  ✗ FAIL")
        tests_failed += 1
    print()

    # Test 4: Empty proof fails
    print("Test 4: Empty proof fails")
    print(f"  Proof: []")
    print(f"  Target: {k_axiom}")
    if not proves([], k_axiom):
        print("  ✓ PASS")
        tests_passed += 1
    else:
        print("  ✗ FAIL")
        tests_failed += 1
    print()

    # Test 5: EFQ proves itself
    proof2 = [efq]
    print("Test 5: EFQ axiom proves itself")
    print(f"  Proof: [{efq}]")
    print(f"  Target: {efq}")
    if proves(proof2, efq):
        print("  ✓ PASS")
        tests_passed += 1
    else:
        print("  ✗ FAIL")
        tests_failed += 1
    print()

    # Test 6: MP witness detection
    bot = Bot()
    line1 = Imp(bot, bot)
    line2 = Imp(line1, bot)
    context = [line1, line2]
    target = bot

    print("Test 6: Modus ponens witness detection")
    print(f"  Context: {[str(f) for f in context]}")
    print(f"  Target: {target}")
    if has_mp_witness(context, target):
        print("  ✓ PASS")
        tests_passed += 1
    else:
        print("  ✗ FAIL")
        tests_failed += 1
    print()

    # Summary
    print("═" * 60)
    print(f"  Tests Passed: {tests_passed}/6")
    print(f"  Tests Failed: {tests_failed}/6")
    print("═" * 60)
    print()

    if tests_failed == 0:
        print("✓ All tests passed!")
        print()
        print("This reference implementation validates the core Hilbert proof")
        print("checking logic independently of the extracted OCaml code.")
        return 0
    else:
        print("✗ Some tests failed")
        return 1


if __name__ == "__main__":
    exit(run_tests())
