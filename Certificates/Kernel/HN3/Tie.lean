module

public import Certificates.Kernel.HN3.Data
public import CFSG.Certificates.Kernel.HN3Sound
public import CFSG.Sporadic.Recognition.HNMult3Data
public import CFSG.Sporadic.Recognition.HNMult3Words

public section

namespace CFSG.KD.HN3

open CFSG.Sporadic.GLQ CFSG.Sporadic.Recognition.HNMult3 CFSG.KS.HN3

theorem prog_eq : prog = hn3Prog.map codeHN3 := by decide +kernel

theorem prog_noPwr : hn3Prog.all (fun ins => !isPwr ins) = true := by decide +kernel

theorem prog_lt : hn3Prog.all (Instr.lt 14) = true := by decide +kernel

theorem rels_eq : rels.map ofCodes3 =
    hn3Rels ++ [hn3Cw 0 ++ [(0, false)], hn3Cw 1 ++ [(1, false)]] := by decide +kernel

theorem codes_lt : (∀ r ∈ rels, ∀ c ∈ r, c < 6) ∧ (∀ r ∈ g2, ∀ c ∈ r, c < 6) ∧
    (∀ r ∈ g3, ∀ c ∈ r, c < 6) ∧ ∀ r ∈ g5, ∀ c ∈ r, c < 6 := by decide +kernel

end CFSG.KD.HN3

end
