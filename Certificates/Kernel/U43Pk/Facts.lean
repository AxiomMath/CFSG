module

public import CFSG.Certificates.Kernel.U43Pk.Sound
public import CFSG.Certificates.Kernel.ArrBfsCert
public import Certificates.Kernel.U43Pk.Pts
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Data
import CFSG.Certificates.Kernel.PackSetSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelU43Pk

open CFSG.KD.U43Pk CFSG.KS.U43Pk CFSG.KS.ArrBfsSim CFSG.Monster.B.Fischer
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

theorem ptAll : ∀ i < 1024, ptK 4 1024 G T E PA LA SO SOI i = true := by
  have hb : ∀ q < 16, u43PkBlk q = true := by
    intro q hq
    interval_cases q
    exacts [u43PkBlk0, u43PkBlk1, u43PkBlk2, u43PkBlk3, u43PkBlk4, u43PkBlk5, u43PkBlk6,
      u43PkBlk7, u43PkBlk8, u43PkBlk9, u43PkBlk10, u43PkBlk11, u43PkBlk12, u43PkBlk13,
      u43PkBlk14, u43PkBlk15]
  intro i hi
  have h := hb (i / 64) (by omega)
  unfold u43PkBlk blkK at h
  have e := CFSG.KC.Pack.allBlk_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  rw [CFSG.KC.Pack.strictB_eq] at e
  have hi' : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [hi'] at e

theorem gensV : ∀ k < 4, rawValidK (G k) = true := by
  intro k hk
  have h := gens
  unfold gensC at h
  have e := CFSG.KC.Pack.allBlk_spec h k hk
  rwa [Nat.add_eq, Nat.zero_add] at e

theorem gensEq : ∀ k < 4, u43Data.gens[k]! = dec (G k) := by decide +kernel

theorem sylowOK_true : sylowOK u43Data = true := by
  have hsz : u43Data.gens.size = 4 := rfl
  have hfuel : u43Data.fuel = 1100 := rfl
  obtain ⟨Tb, hv, h0⟩ := tables_of (n := 4) (N := 1024) (by norm_num) gensEq gensV ptAll
  have hbfs : bfs u43Data = cert 4 1024 (fun i => dec (T i)) E PA LA := by
    unfold bfs
    rw [hsz, hfuel, ← h0]
    exact arrBfs_eq Tb (by norm_num)
  have hok := arrCertOK_cert Tb hv h0
  unfold sylowOK
  rw [hbfs, hsz, cert_pts_size]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨fun k hk => ?_, hok⟩, trivial⟩
  rw [gensEq k hk]
  exact rawValid_dec (gensV k hk)

end CertificateChecks.KernelU43Pk

end
