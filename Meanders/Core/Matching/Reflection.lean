import Meanders.Core.Matching.Dyck

/-!
# Reflection of noncrossing matchings

Reflection is an order-reversing symmetry of the boundary.  It is kept
separate from the local matching surgeries so files that only need symmetry
do not acquire the full surgery API.
-/

namespace Meanders.NoncrossingMatching

variable {j : ℕ}

/-- Reflect a matching across the middle of its boundary. -/
def reflect (m : NoncrossingMatching j) : NoncrossingMatching j :=
  ofPartner (fun v => (m.partner v.mirror).mirror) {
    involutive := fun v => by simp
    ne := fun v h => m.partner_ne v.mirror (by
      apply Point.mirror_injective
      simpa using h)
    noncrossing := fun x u hxu hufx hfxfu => by
      have h₁ : m.partner u.mirror < m.partner x.mirror :=
        Point.mirror_lt_mirror.1 hfxfu
      have h₂ : m.partner x.mirror < u.mirror := Point.mirror_lt_mirror.1 (by
        simpa only [Point.mirror_mirror] using hufx)
      have h₃ : u.mirror < x.mirror := Point.mirror_lt_mirror.2 hxu
      exact m.not_interleave (m.partner_partner u.mirror) (m.partner_partner x.mirror)
        h₁ h₂ h₃ }

@[simp] theorem partner_reflect (m : NoncrossingMatching j) (v : Point j) :
    (reflect m).partner v = (m.partner v.mirror).mirror :=
  partner_ofPartner _ _ _

@[simp] theorem reflect_reflect (m : NoncrossingMatching j) : reflect (reflect m) = m := by
  apply ext_partner
  intro v
  simp

theorem partnerIndex_reflect (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * j) :
    (reflect m).partnerIndex i = 2 * j - 1 - m.partnerIndex (2 * j - 1 - i) := by
  rw [partnerIndex_eq _ hi, partner_reflect]
  have hi' : 2 * j - 1 - i < 2 * j := by omega
  have hmirror : Point.mirror (⟨i, hi⟩ : Point j) = ⟨2 * j - 1 - i, hi'⟩ :=
    Fin.ext (Point.mirror_val _)
  rw [hmirror]
  simp only [Point.mirror_val]
  rw [← m.partnerIndex_eq hi']

end Meanders.NoncrossingMatching
