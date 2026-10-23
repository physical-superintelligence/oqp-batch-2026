module

public import CGLMPBounds.Defs.PartitionSource
public import CGLMPBounds.Defs.ScalarPartition

@[expose] public section


/-! The literal count-probability coefficient in D.3 for the D.10 source
measure. No assertion about an averaged Hardy form is built into this
definition; that geometric identification is a separate obligation. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

def sourcePartitionCoefficient (d h : ℕ) (origin : ℝ) : ℝ :=
  (1 / (2 * (d : ℝ))) * ∫ x in (0 : ℝ)..1, scalarSecant x *
    (sourcePartitionMeasure d).real {T | boundaryArcCount d origin x T = h}

end
end CGLMPBounds.Partition
