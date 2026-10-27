module

public import Certificates.Kernel.W4Row.HeE25K
public import Certificates.Kernel.W4Row.HeE25P
public import Certificates.Kernel.LocalQT.SV.C4134
public import CFSG.Certificates.Kernel.W4Row.EPackKSound
public import CFSG.Certificates.Kernel.W4Row.WordLitKSound

public section

namespace CFSG.KD.W4E.HeE25

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP CFSG.KC.W4E
  CFSG.KC.IntLines CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Setup.X1
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CertificateChecks.KernelLC.HeFix

theorem parse {s : String} (hs : s.toList ∈ strsC) :
    CFSG.Quasithin.B45Exc.Tab.parseInts s = lineInts s.toList :=
  parseInts_str (List.all_eq_true.1 strs _ hs)

theorem gens_perm : ∀ p ∈ [HG.F 0, HG.F 1].zip [G0I, G1I],
    permOK 8330 14 (mask 14) (8330 * 14) p.1 p.2 = true := by
  intro p hp
  have h0 := allN_spec kPL2 0 (by decide)
  have h1 := allN_spec kPL2 1 (by decide)
  simp only [L2_0, L2_1, L2I, List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl
  · exact h0
  · exact h1

theorem id_ok : idK 8330 14 (mask 14) = true := by
  have h := kId
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem lit {wd : List ℤ} {Y YI : ℕ}
    (h : wordLitK 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] wd Y YI = true) :
    PrP 8330 14 (pWord 8330 (unpackP 8330 14 [HG.F 0, HG.F 1] [G0I, G1I]) wd) Y YI :=
  wordLit_of (G := [HG.F 0, HG.F 1]) (GI := [G0I, G1I]) (by norm_num) id_ok rfl gens_perm h

theorem inv_of {t : PArr} {T : ℕ} (e : t = (unpack 8330 14 T, unpack 8330 14 T))
    (h : permOK 8330 14 (mask 14) (8330 * 14) T T = true) : PrP 8330 14 t T T := by
  rw [e]
  exact prp_of_permOK h

theorem check : heE25Check = true := by
  have hn : (8330 : ℕ) < 2 ^ 32 := by norm_num
  have hnw : (8330 : ℕ) ≤ 2 ^ 14 := by norm_num
  have hidn := rs_idn id_ok
  have hi := invs
  simp only [Bool.and_eq_true] at hi
  have hT0 : PrP 8330 14 heT0P (HG.F 0) (HG.F 0) := inv_of (by
    unfold heT0P
    rw [heGen_eq (k := 0) (by decide)]) hi.1.1
  have hT1 : PrP 8330 14 heT1ArrP PT1 PT1 := inv_of (by
    unfold heT1ArrP
    rw [heT1_eq]) hi.1.2
  have hTU : PrP 8330 14 heUP PU PU := inv_of (by
    unfold heUP
    rw [heU_eq]) hi.2
  have hX := lit wX
  unfold heE25Check heWordP heE25WX heE25WY heE25WM1 heE25WM2 heE25WM3 heE25WM4 heE25WM5
    heE25WH0 heE25WH1 heE25WHU
  rw [parse (s := heE25WXStr) (by simp [strsC]), parse (s := heE25WYStr) (by simp [strsC]),
    parse (s := heE25WM1Str) (by simp [strsC]), parse (s := heE25WM2Str) (by simp [strsC]),
    parse (s := heE25WM3Str) (by simp [strsC]), parse (s := heE25WM4Str) (by simp [strsC]),
    parse (s := heE25WM5Str) (by simp [strsC]), parse (s := heE25WH0Str) (by simp [strsC]),
    parse (s := heE25WH1Str) (by simp [strsC]), parse (s := heE25WHUStr) (by simp [strsC]),
    CFSG.KD.LQT.C4134.gens_eq,
    e25Pack_eq hn hnw hidn (rr_of_prp hX).1 (rr_of_prp (lit wY)).1 (lit wM1) (lit wM2) (lit wM3)
      (lit wM4) (lit wM5), pack,
    conjInv_eq hn hnw hT0 (lit wH0) hX, conj0, conjInv_eq hn hnw hT1 (lit wH1) hX, conj1,
    conjInv_eq hn hnw hTU (lit wHU) hX, conjU]
  rfl

end CFSG.KD.W4E.HeE25

end
