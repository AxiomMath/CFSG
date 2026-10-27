
module

public import Certificates.Kernel.UnitarySix.ChainFactsBase

public import Certificates.Kernel.UnitarySix.KQFacts
public import Certificates.Kernel.UnitarySix.ASTQ
public import Certificates.Kernel.UnitarySix.PQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Certificates CFSG.Certificates.Native
open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

namespace CertificateChecks.KernelU6.AQ

theorem arrays :
    ChainArrays aQ (SA.extract 0 9) SA aBase
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 9 12 aDer) := by
  have hlen : aGens.length = 9 := by simp [aGens, aWords]
  have hb := soundBinds letters_eq aWN_eq (by decide) kBinds
  refine certificate_chainArrays (gens := aGens) _ _ _ _ (by rw [hlen]; exact raw)
    (by simp [SA, hlen]) (by simp [SA, hlen]) (fun j hj => ?_) rfl (fun i => ?_)
  · rw [hlen] at hj
    have e : (SA.extract 0 9)[j]! = unpack 693 10 (S j) := by
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    rw [e]
    exact hb j (by simpa [aWords] using hj)
  · fin_cases i <;> rfl

theorem valid : ValidSchreier aQ :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : aQ.orderCertificate = 512 := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 3).map (fun i => rcnt (LR i)) = [32, 8, 2] := by decide
  rw [e] at hs
  exact order_of_sizes rfl (by simp [rawLevels, aBase])
    (validSchreier_of_chainOK arrays (by norm_num) raw).2 hs

end CertificateChecks.KernelU6.AQ

namespace CertificateChecks.KernelU6.SQ

theorem arrays :
    ChainArrays sQ (SA.extract 0 13) SA aBase
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 13 15 sDer) := by
  have hlen : sGens.length = 13 := by simp [sGens, aGens, tGens, aWords, tWords]
  have hb := soundBinds (ws := aWords ++ tWords) letters_eq (by rw [aWN_eq, tWN_eq, List.map_append])
    (by decide) kBinds
  refine certificate_chainArrays (gens := sGens) _ _ _ _ (by rw [hlen]; exact raw)
    (by simp [SA, hlen]) (by simp [SA, hlen]) (fun j hj => ?_) rfl (fun i => ?_)
  · rw [hlen] at hj
    have e : (SA.extract 0 13)[j]! = unpack 693 10 (S j) := by
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    rw [e]
    have := hb j (by simpa [aWords, tWords] using hj)
    have e2 : u62WG u62Letters = u62W := rfl
    simpa [sGens, aGens, tGens, List.map_append, e2] using this
  · fin_cases i <;> rfl

theorem valid : ValidSchreier sQ :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : sQ.orderCertificate = 32768 := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 3).map (fun i => rcnt (LR i)) = [512, 32, 2] := by decide
  rw [e] at hs
  exact order_of_sizes rfl (by simp [rawLevels, aBase])
    (validSchreier_of_chainOK arrays (by norm_num) raw).2 hs

end CertificateChecks.KernelU6.SQ

namespace CertificateChecks.KernelU6.TQ

theorem arrays :
    ChainArrays tQ (SA.extract 0 4) SA tBase
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 5 tDer) := by
  have hlen : tGens.length = 4 := by simp [tGens, tWords]
  have hb := soundBinds letters_eq tWN_eq (by decide) kBinds
  refine certificate_chainArrays (gens := tGens) _ _ _ _ (by rw [hlen]; exact raw)
    (by simp [SA, hlen]) (by simp [SA, hlen]) (fun j hj => ?_) rfl (fun i => ?_)
  · rw [hlen] at hj
    have e : (SA.extract 0 4)[j]! = unpack 693 10 (S j) := by
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    rw [e]
    exact hb j (by simpa [tWords] using hj)
  · fin_cases i <;> rfl

theorem valid : ValidSchreier tQ :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : tQ.orderCertificate = 64 := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 2).map (fun i => rcnt (LR i)) = [16, 4] := by decide
  rw [e] at hs
  exact order_of_sizes rfl (by simp [rawLevels, tBase])
    (validSchreier_of_chainOK arrays (by norm_num) raw).2 hs

end CertificateChecks.KernelU6.TQ

namespace CertificateChecks.KernelU6.PQ

theorem arrays :
    ChainArrays pQ (SA.extract 0 12) SA pBase
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 12 19 pDer) := by
  have hlen : pGens.length = 12 := by simp [pGens, aGens, kGens, aWords, kWords]
  have hb := soundBinds (ws := aWords ++ kWords) letters_eq (by rw [aWN_eq, kWN_eq, List.map_append])
    (by decide) kBinds
  refine certificate_chainArrays (gens := pGens) _ _ _ _ (by rw [hlen]; exact raw)
    (by simp [SA, hlen]) (by simp [SA, hlen]) (fun j hj => ?_) rfl (fun i => ?_)
  · rw [hlen] at hj
    have e : (SA.extract 0 12)[j]! = unpack 693 10 (S j) := by
      rw [getElem!_pos _ j (by simp [SA]; omega)]
      simp [SA]
    rw [e]
    have := hb j (by simpa [aWords, kWords] using hj)
    have e2 : u62WG u62Letters = u62W := rfl
    simpa [pGens, aGens, kGens, List.map_append, e2] using this
  · fin_cases i <;> rfl

theorem valid : ValidSchreier pQ :=
  (validSchreier_of_chainOK arrays (by norm_num) raw).1

theorem order : pQ.orderCertificate = 10321920 := by
  have hs := rawOrbitSizesK_sound binds perm hl
  have e : (List.range 4).map (fun i => rcnt (LR i)) = [21, 512, 120, 8] := by decide
  rw [e] at hs
  exact order_of_sizes rfl (by simp [rawLevels, pBase])
    (validSchreier_of_chainOK arrays (by norm_num) raw).2 hs

end CertificateChecks.KernelU6.PQ

namespace CertificateChecks.KernelU6

theorem chains3010 : chainsCheck = true := by
  simp only [chainsCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨AQ.valid, AQ.order⟩, KQ.valid⟩, KQ.order⟩, PQ.valid⟩, PQ.order⟩, SQ.valid⟩,
    SQ.order⟩, TQ.valid⟩, TQ.order⟩

end CertificateChecks.KernelU6

end
