import Mathlib.Data.Nat.Basic

/-!
# Checking consecutive layers

The cursor records a chain of checked transitions as a proposition, erased
at runtime. It keeps no history of layer data. Any conservation law for the
transition can then be transported along the checked chain.
-/

namespace Meanders.Certify

/-- A layer reached from the initial layer by exactly the checked transitions. -/
inductive CheckedLayers {L : Type} (next : ℕ → L → L) (n : ℕ) (initial : L) : ℕ → L → Prop
  | initial : CheckedLayers next n initial n initial
  | step {r : ℕ} {cur : L} : CheckedLayers next n initial (r + 1) cur →
      CheckedLayers next n initial r (next (r + 1) cur)

/-- A checked prefix, retaining just the current layer and its remaining horizon. -/
structure LayerStream {L : Type} (next : ℕ → L → L) (initial : L) (n : ℕ) where
  /-- Transitions still to check. -/
  remaining : ℕ
  /-- The last checked layer. -/
  layer : L
  /-- The checked transition chain; erased from compiled execution. -/
  checked : CheckedLayers next n initial remaining layer

namespace LayerStream

variable {L : Type} {next : ℕ → L → L} {initial : L} {n : ℕ}

variable [DecidableEq L]

/-- Check layer zero. -/
def start (next : ℕ → L → L) (initial : L) (n : ℕ) (layer : L) :
    Except String (LayerStream next initial n) :=
  if h : layer = initial then
    .ok { remaining := n, layer, checked := by rw [h]; exact .initial }
  else .error "layer 0 is not the initial state"

/-- Compute and compare one successor, with the failing index in the error. -/
def push (s : LayerStream next initial n) (layer : L) :
    Except String (LayerStream next initial n) :=
  match hr : s.remaining with
  | 0 => .error "unexpected layer after the final layer"
  | r + 1 =>
    if h : layer = next (r + 1) s.layer then
      .ok {
        remaining := r
        layer
        checked := by
          rw [h]
          apply CheckedLayers.step
          simpa only [hr] using s.checked }
    else .error s!"layer {n - s.remaining + 1} is not the successor of layer {n - s.remaining}"

/-- Regenerate one exact successor when a compact run omits its payload.
The checked-chain witness is constructed directly, without computing the successor twice. -/
def advance (s : LayerStream next initial n) : Except String (LayerStream next initial n) :=
  match hr : s.remaining with
  | 0 => .error "unexpected layer after the final layer"
  | r + 1 => .ok {
      remaining := r
      layer := next (r + 1) s.layer
      checked := by
        apply CheckedLayers.step
        simpa only [hr] using s.checked }

/-- Check an already-loaded suffix, stopping on its first bad transition, then finish.
The caller owns representation-specific prechecks and terminal normalization. -/
def checkRemaining {Result : Type} (cursor : LayerStream next initial n) (layers : List L)
    (finish : LayerStream next initial n → Except String Result) : Except String Result :=
  match layers.foldlM (fun s layer => s.push layer) cursor with
  | .error message => .error message
  | .ok cursor => finish cursor

/-- A successful loaded check inherits the finisher's proved result. -/
theorem checkRemaining_sound {Result : Type} {property : Result → Prop}
    {cursor : LayerStream next initial n} {layers : List L}
    {finish : LayerStream next initial n → Except String Result} {result : Result}
    (hfinish : ∀ cursor result, finish cursor = .ok result → property result)
    (h : cursor.checkRemaining layers finish = .ok result) : property result := by
  unfold checkRemaining at h
  split at h
  · cases h
  · exact hfinish _ _ h

end LayerStream

end Meanders.Certify
