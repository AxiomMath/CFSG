module

public import Certificates.Kernel.HSMK.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HSMK

open Certificates.ExcModel Certificates.WEMK Certificates.HSMK

@[expose] def hsE : List (List Nat) :=
  [[1, 3, 2, 2, 2, 2], [3, 1, 3, 3, 2, 2], [2, 3, 1, 3, 2, 2], [2, 3, 3, 1, 3, 2], [2, 2, 2, 3, 1, 3],
    [2, 2, 2, 2, 3, 1]]

@[expose] def e12N : List Nat := [1, 12, 0, 0, 0, 0]

theorem k5_rel : (kRel 6 K5.T hsE && kExtra 6 K5.T) = true := by
  decide +kernel

theorem k6_rel : (kRel 6 K6.T hsE && kExtra 6 K6.T) = true := by
  decide +kernel

theorem k5_gen : (kGen 6 K5.T K5.V K5.tab K5.par && kCovK 6 K5.T (ct5N ()) K5.V K5.cov K5.sidx) = true := by
  decide +kernel

theorem k6_gen : (kGen 6 K6.T K6.V K6.tab K6.par && kCovK 6 K6.T (ct6N ()) K6.V K6.cov K6.sidx) = true := by
  decide +kernel

theorem k5_chain : kChain 6 K5.V K5.lv = true := by
  decide +kernel

theorem k5_fix : (K5.T.all fun s => decide (nmv s e12N = e12N)) = true := by
  decide +kernel

theorem k6_orb : kLev 6 K6.V e12N K6.R = true := by
  decide +kernel

theorem k5_lens : (K5.T.length = 5 ∧ K5.lv.map (fun l => l.2.1.length) = [80, 12, 9, 3, 2]) := by
  decide +kernel

theorem k6_lens : (K6.T.length = 6 ∧ K6.R.length = 756) := by
  decide +kernel

end CFSG.KD.HSMK

end
