import BoundariesOfClass.Sieve.Block.Defs
import BoundariesOfClass.Sieve.Block.Base.Pats
import BoundariesOfClass.Sieve.Block.Base.Primes

namespace BoundariesOfClass.Sieve.Block.Gen

def blk_A_00007 : Blk := ⟨0, 10, 1000, 41847, 102, Base.pats, Base.oddPrimes, 0⟩

set_option maxRecDepth 1000000 in
theorem blk_A_00007_ok : blockOK blk_A_00007 = true := by decide +kernel

end BoundariesOfClass.Sieve.Block.Gen
