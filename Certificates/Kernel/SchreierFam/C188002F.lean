module

public import Certificates.Data.HuppertU38.Model
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSchreierFam.U38

open CFSG.RankThree.PartTwo.Sec4.Item434U38 GF64

theorem nAddAssoc : (List.range 64).all (fun x => (List.range 64).all fun y =>
    (List.range 64).all fun z => (((x ^^^ y) % 64) ^^^ z) % 64 == (x ^^^ ((y ^^^ z) % 64)) % 64) =
    true := by
  decide +kernel

@[expose] noncomputable def mulAssocAt (x : Nat) : Bool := (List.range 64).all fun y =>
  (List.range 64).all fun z => mulNat (mulNat x y % 64) z % 64 == mulNat x (mulNat y z % 64) % 64

@[expose] noncomputable def mulAssocB (j : Nat) : Bool := (((List.range 64).drop (j * 4)).take 4).all mulAssocAt

#kc_each mulAssocB 0 16

theorem nMulAssoc : (List.range 64).all (fun x => (List.range 64).all fun y =>
    (List.range 64).all fun z =>
      mulNat (mulNat x y % 64) z % 64 == mulNat x (mulNat y z % 64) % 64) = true := by
  show (List.range 64).all mulAssocAt = true
  refine CFSG.KC.IdxChunks.all_chunks_of _ 4 16 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact mulAssocB0
  | 1, _ => exact mulAssocB1
  | 2, _ => exact mulAssocB2
  | 3, _ => exact mulAssocB3
  | 4, _ => exact mulAssocB4
  | 5, _ => exact mulAssocB5
  | 6, _ => exact mulAssocB6
  | 7, _ => exact mulAssocB7
  | 8, _ => exact mulAssocB8
  | 9, _ => exact mulAssocB9
  | 10, _ => exact mulAssocB10
  | 11, _ => exact mulAssocB11
  | 12, _ => exact mulAssocB12
  | 13, _ => exact mulAssocB13
  | 14, _ => exact mulAssocB14
  | 15, _ => exact mulAssocB15
  | k + 16, h => exact absurd h (by omega)

@[expose] noncomputable def distribAt (x : Nat) : Bool := (List.range 64).all fun y =>
  (List.range 64).all fun z =>
    mulNat x ((y ^^^ z) % 64) % 64 == ((mulNat x y % 64) ^^^ (mulNat x z % 64)) % 64

@[expose] noncomputable def distribB (j : Nat) : Bool := (((List.range 64).drop (j * 4)).take 4).all distribAt

#kc_each distribB 0 16

theorem nDistrib : (List.range 64).all (fun x => (List.range 64).all fun y =>
    (List.range 64).all fun z =>
      mulNat x ((y ^^^ z) % 64) % 64 == ((mulNat x y % 64) ^^^ (mulNat x z % 64)) % 64) = true := by
  show (List.range 64).all distribAt = true
  refine CFSG.KC.IdxChunks.all_chunks_of _ 4 16 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact distribB0
  | 1, _ => exact distribB1
  | 2, _ => exact distribB2
  | 3, _ => exact distribB3
  | 4, _ => exact distribB4
  | 5, _ => exact distribB5
  | 6, _ => exact distribB6
  | 7, _ => exact distribB7
  | 8, _ => exact distribB8
  | 9, _ => exact distribB9
  | 10, _ => exact distribB10
  | 11, _ => exact distribB11
  | 12, _ => exact distribB12
  | 13, _ => exact distribB13
  | 14, _ => exact distribB14
  | 15, _ => exact distribB15
  | k + 16, h => exact absurd h (by omega)

theorem small : (∀ a : GF64, 0 + a = a) ∧ (∀ a : GF64, -a + a = 0) ∧
    (∀ a b : GF64, a * b = b * a) ∧ (∀ a : GF64, 1 * a = a) ∧
    (∀ a : GF64, a ≠ 0 → a * a⁻¹ = 1) ∧ ((0 : GF64)⁻¹ = 0) ∧ (∃ a b : GF64, a ≠ b) := by
  decide +kernel

theorem rootsSU : (∀ k : Fin 6, rootB k + (rootB k).conj8 + rootA k * (rootA k).conj8 = 0) ∧
    ∀ k : Fin 7, SpecialUnitaryM (genMat k) := by
  decide +kernel

end CertificateChecks.KernelSchreierFam.U38
