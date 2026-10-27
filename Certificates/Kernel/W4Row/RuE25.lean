module

public import Certificates.Kernel.W4Row.RuE25K
public import CFSG.Certificates.Kernel.W4Row.InvPackKSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.W4E.RuE25

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP CFSG.KC.W4E
  CFSG.KC.IntLines CFSG.KC.LQT.Cov CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
  CFSG.QuasithinUnique.Bridge.RuExcl CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch.RuG

theorem parse {s : String} (hs : s.toList ∈ strsC) :
    CFSG.Quasithin.B45Exc.Tab.parseInts s = lineInts s.toList :=
  parseInts_str (List.all_eq_true.1 strs _ hs)

theorem gens_eq : [ruA0P, ruA1P] = unpackP 4060 12 [A0, A1] [A0I, A1I] := by
  unfold ruA0P ruA1P
  rw [(inv_of a0_eq pA0).1, (inv_of a1_eq pA1).1, a0_eq, a1_eq]
  rfl

theorem zt_rr : RR 4060 12 ruZtArr (pcomp 4060 12 (mask 12) A1 A1) := by
  have hp : permOK 4060 12 (mask 12) (4060 * 12) A1 A1I = true := pA1
  have h : RR 4060 12 ruA1A A1 := by
    rw [a1_eq]
    exact (rr_of_prp (prp_of_permOK hp)).1
  exact h.comp (by norm_num) (by norm_num) h

theorem check : ruE25Check = true := by
  unfold ruE25Check ruE25WY ruE25WW ruE25WH
  rw [parse (s := ruE25WYStr) (.head _), parse (s := ruE25WWStr) (.tail _ (.head _)),
    parse (s := ruE25WHStr) (.tail _ (.tail _ (.head _))), gens_eq]
  exact invFull_of (τ := ruZtP) zt_rr zt_rr pack

end CFSG.KD.W4E.RuE25

end
