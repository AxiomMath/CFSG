module

public import Certificates.Kernel.ONSeven.RGlue
public import Certificates.Kernel.ONSeven.RChkQ
public import CFSG.Certificates.Kernel.Spor.ONSevenRChecks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.ONR CFSG.KS.ONOrb CFSG.KC.B3S3K
  CFSG.KC.Misc.ArrEnum CFSG.RankThree.Native

theorem qAll_get : ∀ s < (onSevenQArrs ++ onSevenLineArrs).size, ∀ x < 245520,
    ((onSevenQArrs ++ onSevenLineArrs)[s]!)[x]! = qF s x := by
  intro s hs x hx
  rw [qAll_eq] at hs ⊢
  rw [Array.size_map] at hs
  exact words_get qWords_ok hs hx

theorem qAll_size : (onSevenQArrs ++ onSevenLineArrs).size = 59 := by
  rw [qAll_eq, Array.size_map]
  rfl

theorem qArrs_size : onSevenQArrs.size = 2 := by
  unfold onSevenQArrs
  rw [Array.size_map]
  rfl

theorem lineArrs_size : onSevenLineArrs.size = 57 := by
  unfold onSevenLineArrs
  rw [Array.size_map]
  rfl

theorem lt59 {s : Nat} (h : s < 59) : s < nat_lit 59 := h

theorem qOrbit : onSevenQR = Array.ofFn (n := Q.N) fun i => Q.T i.val := by
  unfold onSevenQR
  exact onSevenOrbit_eq (orec_of (k := 2) qArrs_size
    (fun s hs => prefix_get qAll_get s (by rw [qArrs_size]; exact hs)) q_orb
    (fun s hs => qRes_all s (lt59 (by omega))))

theorem q_check : onSevenQCheck onSevenQR onSevenQTabs onSevenLineTabs onSevenQCert = true := by
  have hQN := Nat.eq_of_beq_eq_true q_N
  have hEN := Nat.eq_of_beq_eq_true q_EN
  have hEng := Nat.eq_of_beq_eq_true q_Eng
  have hG0 := q_G0
  have hG1 := q_G1
  have hGp := q_Gp
  have hw := q_w
  have hL := q_L
  have hr : ∀ s < (onSevenQArrs ++ onSevenLineArrs).size, resK Q.N 10 Q.T (qF s) (Q.G s) = true :=
    fun s hs => qRes_all s (lt59 (by rw [qAll_size] at hs; exact hs))
  have hres := resOK_of q_orb qAll_get hr
  have hT := bind_of q_orb (prefix_get qAll_get) (fun s hs => hr s (by simp; omega))
  have hL' := bind_of (gs := onSevenLineArrs) q_orb (suffix_get qAll_get)
    (fun s hs => hr _ (by simp; omega))
  unfold onSevenQCert
  unfold onSevenQTabs onSevenLineTabs
  rw [qOrbit]
  generalize hR : (Array.ofFn (n := Q.N) fun i => Q.T i.val) = R at hres hT hL' ⊢
  have hRs : R.size = 687 := by rw [← hR, Array.size_ofFn, hQN]
  rw [hQN] at hT hL'
  rw [qArrs_size] at hT
  have hGE : BindA 687 10 (onSevenQArrs.map (onSevenTab R)) EQ.ng EQ.G := by
    refine ⟨by rw [hT.1, hEng], fun j hj => ?_⟩
    rw [hEng] at hj
    rw [hT.2 j hj]
    interval_cases j
    · rw [Nat.eq_of_beq_eq_true hG0]
    · rw [Nat.eq_of_beq_eq_true hG1]
  have hGp' : ∀ k < EQ.ng, permB 687 10 (EQ.G k) = true := by
    intro k hk
    rw [hEng] at hk
    have := allN_spec hGp k hk
    interval_cases k
    · rw [Nat.eq_of_beq_eq_true hG0]; exact this
    · rw [Nat.eq_of_beq_eq_true hG1]; exact this
  have hE := enum_of (ps := kbA.toList) (fuel := 400) hGE hGp' EQ.ok
    (fun p hp => by simp [kbA] at hp; omega) EQ.keys (by rw [hEN]; omega)
  have hkeys : kbA.toList = onSevenKeys := rfl
  rw [hkeys] at hE
  rw [hRs]
  refine qcheck_of (PL := QL) hw hRs hres hE.1 (by rw [hE.2.1, hEN]) (fun i hi => hE.2.2 i (by omega))
    (fun i hi => perm_pts hw hGp' EQ.ok i (by omega)) ⟨?_, fun j hj => ?_⟩ ?_
  · rw [hL'.1, lineArrs_size]
  · have hs : j < onSevenLineArrs.size := by
      rw [lineArrs_size]
      exact hj
    rw [hL'.2 j hs, qArrs_size]
    exact congrArg (unpack 687 10) (Nat.eq_of_beq_eq_true (allN_spec hL j hj)).symm
  · rw [← hQN]
    exact q_chk

end CertificateChecks.KernelSpor.ONR

end
