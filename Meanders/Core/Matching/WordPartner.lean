import Meanders.Core.Matching.Dyck
import Meanders.Core.Word.Partner

/-!
# Word scans recover matching partners

Both endpoint directions share the existing geometric-to-Dyck correspondence.
The lemmas are independent of any frontier evaluator or matching surgery.
-/

namespace Meanders.NoncrossingMatching

variable {j : ℕ}

/-- The forward word scan recovers the partner of an opening endpoint. -/
theorem partnerOf_wordOf (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * j)
    (hU : i < m.partnerIndex i) :
    partnerOf m.wordOf i = some (m.partnerIndex i) := by
  have hp := m.partnerIndex_lt hi
  have hmem : (⟨⟨i, hi⟩, ⟨m.partnerIndex i, hp⟩, hU⟩ : Arch j) ∈ m.arches :=
    m.mk_mem_arches hU (Fin.ext (by simp [m.partnerIndex_eq hi]))
  exact partnerOf_eq_of_paired (m.paired_wordOf hmem)

/-- The backward word scan recovers the partner of a closing endpoint. -/
theorem leftPartnerOf_wordOf (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * j)
    (hD : m.partnerIndex i < i) :
    leftPartnerOf m.wordOf i = some (m.partnerIndex i) := by
  have hp := m.partnerIndex_lt hi
  have hmem : (⟨⟨m.partnerIndex i, hp⟩, ⟨i, hi⟩, hD⟩ : Arch j) ∈ m.arches :=
    m.mk_mem_arches hD (Fin.ext (by rw [← m.partnerIndex_eq hp, m.partnerIndex_partnerIndex hi]))
  exact leftPartnerOf_eq_of_paired (m.paired_wordOf hmem)

end Meanders.NoncrossingMatching
