import BoundariesOfClass.Sieve.Block.Defs
import BoundariesOfClass.Sieve.Block.Base.Pats
import BoundariesOfClass.Sieve.Block.Base.Primes

namespace BoundariesOfClass.Sieve.Block.Gen

def blk_B2_00001 : Blk := ⟨1, 10, 1000, 7462, 86, Base.pats, Base.oddPrimes, 0⟩

set_option maxRecDepth 1000000 in
theorem blk_B2_00001_ok : blockOK blk_B2_00001 = true := by decide +kernel

end BoundariesOfClass.Sieve.Block.Gen
