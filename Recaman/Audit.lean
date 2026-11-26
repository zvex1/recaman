import Recaman.Wilks
import Recaman.Open
import Recaman.Cascade
import Recaman.Sweep

/-! Axiom audit for the modules beyond `Recaman.lean` (which audits itself). Everything prints
only `propext`, `Classical.choice`, `Quot.sound`, except the three theorems resting on the
`native_decide` run, which also show `check_wilks._native.native_decide.ax_1_1`. -/

#print axioms Recaman.clock_fwd
#print axioms Recaman.clock_back
#print axioms Recaman.clock_fwd_wrap
#print axioms Recaman.clock_back_wrap
#print axioms Recaman.wrap_iff
#print axioms Recaman.wrap_between
#print axioms Recaman.wrap_infinitely_often
#print axioms Recaman.below_diag_antitone
#print axioms Recaman.fill_iff
#print axioms Recaman.IT.insRange_spec
#print axioms Recaman.run_spec
#print axioms Recaman.check2_sound
#print axioms Recaman.occur_below_1355
#print axioms Recaman.back_count
#print axioms Recaman.off_add_slev
#print axioms Recaman.nwrap_pow_three
#print axioms Recaman.nwrap_double
#print axioms Recaman.nback_pow_two
#print axioms Recaman.density_of_levelBounded
#print axioms Recaman.wilks
#print axioms Recaman.fate_852655
#print axioms Recaman.restart_jump_index
#print axioms Recaman.one_chance
#print axioms Recaman.lev_ne_zero_in_window
#print axioms Recaman.fwd_in_window
#print axioms Recaman.occurs_852655_iff
