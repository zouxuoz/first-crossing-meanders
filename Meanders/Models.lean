import Meanders.Models.FirstCrossing.Original.Cut
import Meanders.Models.FirstCrossing.Original.Exterior
import Meanders.Models.FirstCrossing.Original.ForcedPrefix
import Meanders.Models.FirstCrossing.Original.Pairing
import Meanders.Models.FirstCrossing.Original.Schedule
import Meanders.Models.FirstCrossing.Original.Source
import Meanders.Models.FirstCrossing.Native.Bounds
import Meanders.Models.FirstCrossing.Native.Codec
import Meanders.Models.FirstCrossing.Native.Geometry
import Meanders.Models.FirstCrossing.Native.PortBound
import Meanders.Models.FirstCrossing.Native.Stage
import Meanders.Models.FirstCrossing.Native.State
import Meanders.Models.FirstCrossing.Surgery.Closure
import Meanders.Models.FirstCrossing.Surgery.Coverage
import Meanders.Models.FirstCrossing.Surgery.Cup
import Meanders.Models.FirstCrossing.Surgery.Drain
import Meanders.Models.FirstCrossing.Surgery.DrainTotal
import Meanders.Models.FirstCrossing.Surgery.NativeTotal
import Meanders.Models.FirstCrossing.Surgery.Normalize
import Meanders.Models.FirstCrossing.Surgery.PhysicalCyclic
import Meanders.Models.FirstCrossing.Surgery.VisitCoverage
import Meanders.Models.FirstCrossing.Interpretation.AttachmentStep
import Meanders.Models.FirstCrossing.Interpretation.Boundary
import Meanders.Models.FirstCrossing.Interpretation.FIFO
import Meanders.Models.FirstCrossing.Interpretation.Invariant
import Meanders.Models.FirstCrossing.Interpretation.Preservation
import Meanders.Models.FirstCrossing.Interpretation.SourceCoverage
import Meanders.Models.FirstCrossing.Interpretation.SourceCycle
import Meanders.Models.FirstCrossing.Interpretation.SourceProgress
import Meanders.Models.FirstCrossing.Interpretation.SourceStep
import Meanders.Models.FirstCrossing.Correctness.AcceptedWeight
import Meanders.Models.FirstCrossing.Correctness.Future
import Meanders.Models.FirstCrossing.Correctness.JointCorrect
import Meanders.Models.FirstCrossing.Packed.Correct

/-! Umbrella for the Models layer: alternative finite descriptions of the
problems, each with its bridge. Imports only. -/
