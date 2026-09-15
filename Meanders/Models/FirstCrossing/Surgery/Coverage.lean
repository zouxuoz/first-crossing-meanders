import Meanders.Models.FirstCrossing.Surgery.Splice

/-!
# Coverage of physical vertices during named joins

Live endpoint paths alone do not describe components that have lost every
frontier port. Coverage retains a physical witness each time a represented path
closes. This is a coverage invariant, not yet a proof that these witnesses lie
in distinct permanent components of the completed source graph.
-/

namespace Meanders.FirstCrossing

/-- Every processed physical vertex belongs to a represented live path or to
one of the components whose last two ports have already been consumed. -/
def CoversProcessed {V : Type*} (mate : List (Option ℕ)) (G : SimpleGraph V)
    (port : ℕ → V) (closed : List V) (processed : V → Prop) : Prop :=
  ∀ v, processed v →
    (∃ i, Live mate i ∧ G.Reachable (port i) v) ∨
    (∃ c ∈ closed, G.Reachable c v)

/-- In a nonclosing join, either an old live witness survives, or its mate
survives and reaches the same physical component. -/
theorem rewireJoined_covers {V : Type*} {mate : List (Option ℕ)}
    {G : SimpleGraph V} {port : ℕ → V} {closed : List V} {processed : V → Prop}
    (hm : MateInvariant mate) (hp : RepresentsLivePaths mate G port)
    (hc : CoversProcessed mate G port closed processed)
    {x y a b : ℕ} (hx : HasMate mate x a) (hy : HasMate mate y b)
    (hxy : x ≠ y) (hay : a ≠ y) :
    CoversProcessed (rewireJoined mate x y a b)
      (G ⊔ SimpleGraph.edge (port x) (port y)) port closed processed := by
  have hmono := SimpleGraph.Reachable.mono'
    (show G ≤ G ⊔ SimpleGraph.edge (port x) (port y) from le_sup_left)
  obtain ⟨hax, hay, hbx, hby, -⟩ := hm.splice_distinct hx hy hxy hay
  intro v hv
  rcases hc v hv with ⟨i, hi, hiv⟩ | ⟨c, hmem, hcv⟩
  · left
    by_cases hix : i = x
    · subst i
      refine ⟨a, (rewireJoined_live hm hx hy hxy hay).mpr
        ⟨⟨x, hm.symm hx⟩, hax, hay⟩, hmono _ _ ?_⟩
      exact ((hp a x ⟨x, hm.symm hx⟩ ⟨a, hx⟩).mpr
        (Or.inr (hm.symm hx))).trans hiv
    by_cases hiy : i = y
    · subst i
      refine ⟨b, (rewireJoined_live hm hx hy hxy hay).mpr
        ⟨⟨y, hm.symm hy⟩, hbx, hby⟩, hmono _ _ ?_⟩
      exact ((hp b y ⟨y, hm.symm hy⟩ ⟨b, hy⟩).mpr
        (Or.inr (hm.symm hy))).trans hiv
    exact ⟨i, (rewireJoined_live hm hx hy hxy hay).mpr ⟨hi, hix, hiy⟩,
      hmono _ _ hiv⟩
  · exact Or.inr ⟨c, hmem, hmono _ _ hcv⟩

/-- Closing a represented path retains `port x` as a witness for all its
physical vertices, including vertices that no longer reach a live endpoint. -/
theorem eraseJoined_covers {V : Type*} {mate : List (Option ℕ)}
    {G : SimpleGraph V} {port : ℕ → V} {closed : List V} {processed : V → Prop}
    (hm : MateInvariant mate) (hp : RepresentsLivePaths mate G port)
    (hc : CoversProcessed mate G port closed processed)
    {x y : ℕ} (hx : HasMate mate x y) :
    CoversProcessed (eraseJoined mate x y)
      (G ⊔ SimpleGraph.edge (port x) (port y)) port (port x :: closed) processed := by
  have hy := hm.symm hx
  have hmono := SimpleGraph.Reachable.mono'
    (show G ≤ G ⊔ SimpleGraph.edge (port x) (port y) from le_sup_left)
  intro v hv
  rcases hc v hv with ⟨i, hi, hiv⟩ | ⟨c, hmem, hcv⟩
  · by_cases hix : i = x
    · subst i
      exact Or.inr ⟨port x, by simp, hmono _ _ hiv⟩
    by_cases hiy : i = y
    · subst i
      refine Or.inr ⟨port x, by simp, hmono _ _ ?_⟩
      exact ((hp x y ⟨y, hx⟩ ⟨x, hy⟩).mpr (Or.inr hx)).trans hiv
    exact Or.inl ⟨i, (eraseJoined_live hx.bound hy.bound).mpr ⟨hi, hix, hiy⟩,
      hmono _ _ hiv⟩
  · exact Or.inr ⟨c, by simp [hmem], hmono _ _ hcv⟩

/-- The actual executable join preserves coverage and the exact number of
recorded closed-component witnesses. No output validity is assumed. -/
theorem spliceJoin_covers {V : Type*} {w out : Splice}
    {G : SimpleGraph V} {port : ℕ → V} {closed : List V} {processed : V → Prop}
    (hm : MateInvariant w.mate) (hp : RepresentsLivePaths w.mate G port)
    (hc : CoversProcessed w.mate G port closed processed)
    (hcount : closed.length = w.cycles)
    {x y a b : ℕ} (hx : HasMate w.mate x a) (hy : HasMate w.mate y b)
    (hxy : x ≠ y) (h : spliceJoin w x y = some out) :
    ∃ closed',
      CoversProcessed out.mate (G ⊔ SimpleGraph.edge (port x) (port y))
        port closed' processed ∧
      closed'.length = out.cycles ∧
      closed' = if a = y then port x :: closed else closed := by
  by_cases hay : a = y
  · subst a
    rw [spliceJoin_eq_close hxy hx (hm.symm hx)] at h
    cases h
    exact ⟨port x :: closed, eraseJoined_covers hm hp hc hx,
      by simpa using hcount, by simp⟩
  · rw [spliceJoin_eq_rewire hm hx hy hxy hay] at h
    cases h
    exact ⟨closed, rewireJoined_covers hm hp hc hx hy hxy hay, hcount, by simp [hay]⟩

/-- Once every vertex is processed, one closed witness and no live ports
establish connectedness. The witness also establishes nonemptiness. -/
theorem CoversProcessed.connected_singleton {V : Type*} {mate : List (Option ℕ)}
    {G : SimpleGraph V} {port : ℕ → V} {processed : V → Prop} {c : V}
    (hc : CoversProcessed mate G port [c] processed)
    (hempty : ∀ i, ¬ Live mate i) (hall : ∀ v, processed v) : G.Connected := by
  have reach : ∀ v, G.Reachable c v := by
    intro v
    rcases hc v (hall v) with ⟨i, hi, -⟩ | ⟨d, hd, hdv⟩
    · exact False.elim (hempty i hi)
    · have he : d = c := by simpa using hd
      simpa [he] using hdv
  let : Nonempty V := ⟨c⟩
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

/-- The counter form of terminal coverage: one recorded cycle provides the
unique closed witness, so a separate inhabitant assumption is unnecessary. -/
theorem CoversProcessed.connected_of_one_cycle {V : Type*} {w : Splice}
    {G : SimpleGraph V} {port : ℕ → V} {closed : List V} {processed : V → Prop}
    (hc : CoversProcessed w.mate G port closed processed)
    (hcount : closed.length = w.cycles) (hone : w.cycles = 1)
    (hempty : ∀ i, ¬ Live w.mate i) (hall : ∀ v, processed v) : G.Connected := by
  have hlen : closed.length = 1 := hcount.trans hone
  cases closed with
  | nil => simp at hlen
  | cons c rest =>
    have hr : rest = [] := by simpa using hlen
    subst rest
    exact hc.connected_singleton hempty hall

end Meanders.FirstCrossing
