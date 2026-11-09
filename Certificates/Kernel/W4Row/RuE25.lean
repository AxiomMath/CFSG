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

theorem lines : e25LinesK 5 6 ruE25Conj = true := by decide +kernel

theorem pack : invSlpK 4060 12 5 [A0, A1] [A0I, A1I] (pcomp 4060 12 (mask 12) A1 A1)
    (pcomp 4060 12 (mask 12) A1 A1) ruE25Prog 68 101 123 ruE25Conj = true := by
  unfold invSlpK
  rw [ruE25IdOK, ruE25GensOK, ruE25Prog_split, runP_append, runP_append, runP_ckpt ruE25Pack1,
    runP_ckpt ruE25Pack2]
  exact ruE25Pack3

theorem check : ruE25Check = true := by
  unfold ruE25Check ruE25WY ruE25WW ruE25WH
  rw [parse (s := ruE25WYStr) (.head _), parse (s := ruE25WWStr) (.tail _ (.head _)),
    parse (s := ruE25WHStr) (.tail _ (.tail _ (.head _))), gens_eq]
  have hw := words
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hw
  have hwf : ∀ k (hk : k < ruE25Prog.length),
      (ruE25Prog[k].1).natAbs ≤ k + 2 ∧ (ruE25Prog[k].2).natAbs ≤ k + 2 := by
    decide +kernel
  exact invSlp_of (τ := ruZtP) (ky := 68) (kw := 101) (kh := 123) (f := 50) zt_rr zt_rr rfl hwf
    h1 h2 h3 h4 h5 h6 pack lines

end CFSG.KD.W4E.RuE25

end
