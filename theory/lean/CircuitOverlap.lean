/-
# Circuit overlap as a predictor of per-instance correctness

The card scores each hidden unit by attribution, takes the top-K units as a
"circuit", and predicts whether the model will get an item right from the
Jaccard overlap between that item's circuit and a reference circuit. The claim
is that the resulting AUC clears a threshold.

Two facts about the overlap are proved here, and they bound where the method is
sound. `jaccard_self` and `jaccard_comm` are the easy ones. The one that
matters is what is NOT here: nothing says the overlap is a property of the
FUNCTION the network computes rather than of its parameterization. Hidden units
carry a permutation symmetry, and a per-unit attribution moves with it. Within
one model the reference and the item circuit permute together and the overlap
is unchanged -- which is the deployed use, and is sound. Across two
independently trained models it is not, and that is stated as an open question
in `AIQ.Conjectures.Circuits`, not resolved here.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace AIQ.Teams.CircuitOverlap

variable {α : Type*} [DecidableEq α]

/-- Jaccard overlap of two circuits. Zero on two empty circuits, which the card
never produces: `top_k` with `k > 0` is nonempty. -/
noncomputable def jaccard (A B : Finset α) : ℝ :=
  ((A ∩ B).card : ℝ) / ((A ∪ B).card : ℝ)

/-- Overlap does not depend on the order of its arguments. -/
theorem jaccard_comm (A B : Finset α) : jaccard A B = jaccard B A := by
  unfold jaccard
  rw [Finset.inter_comm, Finset.union_comm]

/-- A circuit overlaps itself completely. -/
theorem jaccard_self {A : Finset α} (hA : A.Nonempty) : jaccard A A = 1 := by
  unfold jaccard
  rw [Finset.inter_self, Finset.union_self]
  exact div_self (Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hA.choose_spec))

/-- Overlap is bounded by one: the intersection is contained in the union. -/
theorem jaccard_le_one (A B : Finset α) : jaccard A B ≤ 1 := by
  unfold jaccard
  rcases Finset.eq_empty_or_nonempty (A ∪ B) with h | h
  · simp [Finset.union_eq_empty.mp h]
  · rw [div_le_one (by exact_mod_cast Finset.card_pos.mpr h)]
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_union)

/-- The card's assertion: the predictor's AUC clears a threshold. A definition
-- whether it holds is what the run measures. Above-chance means `θ > 1/2`. -/
def AUCExceeds (auc θ : ℝ) : Prop := auc ≥ θ

end AIQ.Teams.CircuitOverlap
