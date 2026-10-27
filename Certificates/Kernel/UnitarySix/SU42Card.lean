module

public import Certificates.Kernel.UnitarySix.SU42C
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Monster.B.Mathieu.Order
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Certificate3195Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (genBits bmulVec toMat toVec bz bitsOf testBit_bitsOf
  toVec_bmulVec toMat_bmul toMat_eq_one_of_bIsId bmul)
open Matrix

namespace SU42C

theorem perm : allN 9 (fun j => permOK 256 9 (mask 9) (256 * 9) (S j) (SI j)) = true := by
  quickRfl

@[expose] noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 9) fun j => unpack 256 9 (S j.val)

theorem SA_size : SA.size = 9 := by simp [SA]

theorem binds : Binds 256 9 S 9 4 BP SA su42Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem raw : rawChainOK 256 (SA.extract 0 2) SA su42Base
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 su42Der) 1 = true :=
  rawChainK_sound (NS := 8) (CH := 32) binds head hl (by norm_num) hs

theorem orbits : rawOrbitSizes 256 SA su42Base = [135, 12, 8, 2] := by
  rw [rawOrbitSizesK_sound binds perm hl]
  decide

theorem gen_entry (s : Fin 2) (x : Fin 256) :
    (SA[s.val]!)[x.val]! = bmulVec 8 8 (genBits (Fin.ofNat 3 s.val)) x.val := by
  have h : ∀ s : Fin 2, ∀ x : Fin 256,
      pg 9 (mask 9) (S s.val) x.val = bmulVec 8 8 (genBits (Fin.ofNat 3 s.val)) x.val := by
    decide +kernel
  rw [SA, getElem!_pos _ s.val (by simp; omega), Array.getElem_ofFn]
  simp only [unpack]
  rw [getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
  exact h s x

end SU42C

@[expose] def codeV (v : Fin 8 → ZMod 2) : ℕ :=
  bitsOf 8 fun i => if h : i < 8 then (v ⟨i, h⟩).val == 1 else false

theorem codeV_lt (v : Fin 8 → ZMod 2) : codeV v < 256 := by
  apply Nat.lt_pow_two_of_testBit (n := 8)
  intro i hi
  rw [codeV, testBit_bitsOf]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hi

theorem toVec_codeV (v : Fin 8 → ZMod 2) : toVec 8 (codeV v) = v := by
  funext i
  rw [toVec, codeV, testBit_bitsOf]
  simp only [i.isLt, decide_true, Bool.true_and, dite_true, Fin.eta]
  generalize v i = a
  fin_cases a <;> rfl

theorem codeV_toVec {c : ℕ} (hc : c < 256) : codeV (toVec 8 c) = c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [codeV, testBit_bitsOf]
  by_cases hj : j < 8
  · simp only [hj, decide_true, Bool.true_and, dite_true, toVec]
    cases c.testBit j <;> rfl
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc
      (Nat.pow_le_pow_right (n := 2) (by norm_num) (not_lt.mp hj)))).symm

@[expose] def vecEquiv : (Fin 8 → ZMod 2) ≃ Fin 256 where
  toFun v := ⟨codeV v, codeV_lt v⟩
  invFun p := toVec 8 p.val
  left_inv v := toVec_codeV v
  right_inv p := Fin.ext (codeV_toVec p.isLt)

@[expose] noncomputable def rhoV : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) →*
    Equiv.Perm (Fin 8 → ZMod 2) where
  toFun g :=
    { toFun := fun v => (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v
      invFun := fun v => ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v
      left_inv := fun v => by simp [mulVec_mulVec]
      right_inv := fun v => by simp [mulVec_mulVec] }
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp [mulVec_mulVec]

@[expose] noncomputable def rho : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) →*
    Equiv.Perm (Fin 256) where
  toFun g := vecEquiv.permCongr (rhoV g)
  map_one' := by ext p; simp [Equiv.permCongr_apply]
  map_mul' g h := by ext p; simp [Equiv.permCongr_apply]

theorem rho_apply (g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) (p : Fin 256) :
    rho g p = vecEquiv ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ toVec 8 p.val) := rfl

theorem rho_injective : Function.Injective rho := by
  intro g h hgh
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have := congrArg (fun f : Equiv.Perm (Fin 256) => vecEquiv.symm (f (vecEquiv v))) hgh
  simpa [rho_apply, vecEquiv, toVec_codeV, Matrix.toLin'_apply] using this

@[expose] noncomputable def xGL : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  ⟨toMat 8 8 (genBits 0), toMat 8 8 (genBits 0), by
      rw [← toMat_bmul]; exact toMat_eq_one_of_bIsId (by decide +kernel),
    by rw [← toMat_bmul]; exact toMat_eq_one_of_bIsId (by decide +kernel)⟩

@[expose] noncomputable def yGL : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  ⟨toMat 8 8 (genBits 1), toMat 8 8 (genBits 2), by
      rw [← toMat_bmul]; exact toMat_eq_one_of_bIsId (by decide +kernel),
    by rw [← toMat_bmul]; exact toMat_eq_one_of_bIsId (by decide +kernel)⟩

theorem rho_eq {g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)} (s : Fin 2)
    (hg : (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) = toMat 8 8 (genBits (Fin.ofNat 3 s.val))) :
    rho g = permOfArr 256 SU42C.SA[s.val]! := by
  refine (CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep fun x => ?_).symm
  rw [SU42C.gen_entry s x, rho_apply, hg, ← toVec_bmulVec]
  simp only [vecEquiv, Equiv.coe_fn_mk]
  rw [codeV_toVec]
  apply Nat.lt_pow_two_of_testBit (n := 8)
  intro i hi
  rw [bmulVec, testBit_bitsOf]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hi

theorem suClosure_eq : Certificates.suClosure = Subgroup.closure {xGL, yGL} := by
  unfold Certificates.suClosure
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem map_suClosure : Certificates.suClosure.map rho =
    Subgroup.closure {g | ∃ k < (SU42C.SA.extract 0 2).size,
      permOfArr 256 (SU42C.SA.extract 0 2)[k]! = g} := by
  rw [suClosure_eq, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq]
  have hs : (SU42C.SA.extract 0 2).size = 2 := by simp [SU42C.SA]
  have he : ∀ k < 2, (SU42C.SA.extract 0 2)[k]! = SU42C.SA[k]! := by
    intro k hk
    rw [getElem!_pos _ k (by omega), getElem!_pos _ k (by rw [SU42C.SA_size]; omega),
      Array.getElem_extract]
    simp
  have h0 : rho xGL = permOfArr 256 SU42C.SA[0]! := rho_eq 0 rfl
  have h1 : rho yGL = permOfArr 256 SU42C.SA[1]! := rho_eq 1 rfl
  rw [hs]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by rw [he 0 (by norm_num), h0]⟩
    · exact ⟨1, by norm_num, by rw [he 1 (by norm_num), h1]⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (by rw [he 0 (by norm_num), h0])
    · exact Or.inr (by rw [he 1 (by norm_num), h1])

theorem card_suClosure : Nat.card Certificates.suClosure = 25920 := by
  rw [← Subgroup.card_map_of_injective rho_injective, map_suClosure]
  have hb : ([1, 4, 16, 64] : List (Fin 256)).Nodup := by decide
  have hbase : (([1, 4, 16, 64] : List (Fin 256)).map Fin.val).toArray = su42Base := rfl
  have hs : (SU42C.SA.extract 0 2).size = 2 := by simp [SU42C.SA]
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 256) (by norm_num)
    (O := SU42C.SA.extract 0 2) (S := SU42C.SA)
    (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 su42Der) hb (chunks := 1) (by norm_num)
    (by simp [SU42C.SA]) (fun i hi => by
      rw [hs] at hi
      rw [getElem!_pos _ i (by rw [SU42C.SA_size]; omega), getElem!_pos _ i (by rw [hs]; omega),
        Array.getElem_extract]
      simp)
    (by rw [hs, hbase]; exact SU42C.raw)
  rw [h, hbase, SU42C.orbits]
  rfl

end CertificateChecks.KernelU6
