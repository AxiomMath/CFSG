module

public import Certificates.Kernel.Tc.M24
public import CFSG.Certificates.Kernel.TcKSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.M24

open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K CFSG.KC.TcK CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.Monster.B.Mathieu

theorem hw : szOK 24 5 = true := by decide +kernel

theorem hkeys : keys.toList = List.range 24 := by decide +kernel

theorem hkeys6 : keys6.toList = List.range 6 := by decide +kernel

theorem hps : ∀ p ∈ keys.toList, p < 24 := by
  rw [hkeys]
  intro p hp
  exact List.mem_range.1 hp

theorem hps6 : ∀ p ∈ keys6.toList, p < 6 := by
  rw [hkeys6]
  intro p hp
  exact List.mem_range.1 hp

theorem bind_of {a : Array (Array Nat)} {m n w : Nat} {F : Nat → Nat} {g : Nat}
    (hs : a.size = m) (hg : g = m) (h : ∀ j < m, arrBind a[j]! n w (F j) = true) :
    BindA n w a g F := by
  subst hg
  exact ⟨hs, fun j hj => arrBind_sound (h j hj)⟩

theorem perm_of {m n w g : Nat} {F : Nat → Nat} (hg : g = m)
    (h : allN m (fun k => permB n w (F k)) = true) : ∀ k < g, permB n w (F k) = true := by
  subst hg
  exact allN_spec h

@[expose] def EnumF (gs : Array (Array Nat)) (fuel N : Nat) (T : Nat → Nat) : Prop :=
  enumOK 24 gs (List.range 24) (enumBfs 24 gs (List.range 24) fuel) = true ∧
    (enumBfs 24 gs (List.range 24) fuel).pts.size = N ∧
    ∀ i < N, (enumBfs 24 gs (List.range 24) fuel).pts[i]! = unpack 24 5 (T i)

theorem eQ : EnumF gQ 1200 EQ.N EQ.T := by
  have h := enum_of (fuel := 1200) (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.1) bQ)
    (perm_of (Nat.eq_of_beq_eq_true ns.1) gperm.1) EQ.ok hps EQ.keys (by decide +kernel)
  rw [hkeys] at h
  exact h

theorem eK : EnumF gK 250 EK.N EK.T := by
  have h := enum_of (fuel := 250) (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.2.1) bK)
    (perm_of (Nat.eq_of_beq_eq_true ns.2.1) gperm.2.1) EK.ok hps EK.keys (by decide +kernel)
  rw [hkeys] at h
  exact h

theorem eC : EnumF m24caA 1200 EC.N EC.T := by
  have h := enum_of (fuel := 1200)
    (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.2.2.1) bC)
    (perm_of (Nat.eq_of_beq_eq_true ns.2.2.1) gperm.2.2.1) EC.ok hps EC.keys (by decide +kernel)
  rw [hkeys] at h
  exact h

theorem eY : EnumF m24sA 40 EY.N EY.T := by
  have h := enum_of (fuel := 40)
    (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.2.2.2.1) bY)
    (perm_of (Nat.eq_of_beq_eq_true ns.2.2.2.1) gperm.2.2.2.1) EY.ok hps EY.keys
    (by decide +kernel)
  rw [hkeys] at h
  exact h

theorem eS : enumOK 6 sig (List.range 6) (enumBfs 6 sig (List.range 6) 500) = true ∧
    (enumBfs 6 sig (List.range 6) 500).pts.size = ES.N := by
  have h := enum_of (fuel := 500)
    (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.2.2.2.2) bS)
    (perm_of (Nat.eq_of_beq_eq_true ns.2.2.2.2) gperm.2.2.2.2) ES.ok hps6 ES.keys
    (by decide +kernel)
  rw [hkeys6] at h
  exact ⟨h.1, h.2.1⟩

theorem hMS (j : Nat) (hj : j < 11) : misc[j]! = unpack 24 5 (MS j) := arrBind_sound (bMS j hj)

theorem bCU : BindA 24 5 m24TcD.cu 2 MS :=
  ⟨by decide +kernel, fun j hj => by
    rw [← hMS j (by omega)]
    interval_cases j <;> rfl⟩

theorem bCV : BindA 24 5 m24TcD.cv 2 (fun i => MS (Nat.add 2 i)) :=
  ⟨by decide +kernel, fun j hj => by
    rw [← hMS (Nat.add 2 j) (by change 2 + j < 11; omega)]
    interval_cases j <;> rfl⟩

theorem bR : BindA 24 5 m24TcD.reps 6 (fun j => MS (Nat.add 4 j)) :=
  ⟨by decide +kernel, fun j hj => by
    rw [← hMS (Nat.add 4 j) (by change 4 + j < 11; omega)]
    interval_cases j <;> rfl⟩

theorem hx : m24xA = unpack 24 5 (MS 10) := by
  rw [← hMS 10 (by norm_num)]
  rfl

theorem tc : tcOK 24 6 (List.range 24) m24xA m24TcD (m24TcCQ ()) (m24TcCK ()) (m24TcCS ()) =
    true := by
  have hQ := eQ
  have hK := eK
  have hS := eS
  have hTQ : ∀ i < EQ.N, permB 24 5 (EQ.T i) = true := allN_spec EQ.perm
  have hTK : ∀ i < EK.N, permB 24 5 (EK.T i) = true := allN_spec EK.perm
  exact tcOK_of_K hw hx
    (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.1) bQ) bCU bCV
    (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.2.1) bK) bR
    (by rw [Nat.eq_of_beq_eq_true ns.1]; decide +kernel) (fun i _ j _ => rfl)
    hQ.1 hQ.2.1 hQ.2.2 hTQ hK.1 hK.2.1 hK.2.2 hTK hS.1 hS.2 rest

theorem m24Tc_ok : m24TcOK () = true := by
  have hC := eC
  have hY := eY
  have hNY : EY.N = 27 := Nat.eq_of_beq_eq_true nY
  have hin : allLt m24TcD.gQ.size (fun l => (m24CC ()).pts.toList.any (eqA 24 m24TcD.gQ[l]!)) =
      true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro l hl
    have hl2 : l < 2 := by simpa [m24TcD] using hl
    have hg : m24TcD.gQ[l]! = unpack 24 5 (EQ.G l) :=
      (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true ns.1) bQ).2 l
        (by rw [Nat.eq_of_beq_eq_true ns.1]; exact hl2)
    rw [hg]
    exact any_of_memK hC.2.1 hC.2.2 (allN_spec inC l hl2)
  have hcube : allLt (m24SC ()).pts.size
      (fun k => eqA 24 (powArr 24 (m24SC ()).pts[k]! 3) (idA 24)) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    change k < (enumBfs 24 m24sA (List.range 24) 40).pts.size at hk
    rw [hY.2.1] at hk
    change eqA 24 (powArr 24 (enumBfs 24 m24sA (List.range 24) 40).pts[k]! 3) (idA 24) = true
    rw [hY.2.2 k hk, powEq_id hw (allN_spec EY.perm k hk)]
    exact allN_spec cubeY k hk
  unfold m24TcOK
  rw [tc]
  change (true && enumOK 24 m24caA (List.range 24) (enumBfs 24 m24caA (List.range 24) 1200) &&
    _ && enumOK 24 m24sA (List.range 24) (enumBfs 24 m24sA (List.range 24) 40) &&
    ((enumBfs 24 m24sA (List.range 24) 40).pts.size == 27) && _) = true
  rw [hC.1, hY.1, hY.2.1, hNY, hin, hcube]
  rfl

end CertificateChecks.KernelTc.M24

end
