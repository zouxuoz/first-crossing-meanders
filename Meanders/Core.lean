import Meanders.Core.Matching.WordPartner
import Meanders.Core.Permutation.FiniteSupport
import Meanders.Core.Graph.ClosedSets
import Meanders.Core.Word.Balanced
import Meanders.Core.Word.Intrinsic.Height
import Meanders.Core.Word.Intrinsic.Reflection
import Meanders.Core.Arch
import Meanders.Core.Graph.Pairing
import Meanders.Core.Graph.Flood
import Meanders.Core.Graph.SupEdge
import Meanders.Core.Matching
import Meanders.Core.Matching.Exterior
import Meanders.Core.Matching.Prefix
import Meanders.Core.Matching.Dyck
import Meanders.Core.Matching.Reflection
import Meanders.Core.Matching.Surgery
import Meanders.Core.Overlay
import Meanders.Core.Overlay.Cut
import Meanders.Core.Word
import Meanders.Core.Word.Splice
import Meanders.Core.Word.Bits
import Meanders.Core.Word.Partner

/-! Umbrella for the Core layer: reusable combinatorial objects (arches,
noncrossing matchings and their surgeries, balanced words, overlays, graph
tools) and their enumerations. Imports only. -/
