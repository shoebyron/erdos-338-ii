import CollisionDensity
import ProgressionFromKneser

namespace Erdos338.Bridge

/-- The paper's infinite-sumset route reduces the problem to asymptotic Kneser alone. -/
theorem boundedByOrder_of_asymptoticKneser (kneser : AsymptoticKneser) : BoundedByOrder :=
  boundedByOrder_of_analyticInputs uniformDensityInput (progressionInput_of_asymptoticKneser kneser)

#check boundedByOrder_of_asymptoticKneser
#print axioms boundedByOrder_of_asymptoticKneser

end Erdos338.Bridge

