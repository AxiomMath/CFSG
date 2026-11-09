module

public import Certificates.Data.Kernel.PermCent.A6BTwin
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.A6B

theorem k5159P : ((elemsC QP).all fun g => orderIsP g 1 [] || orderIsP g 2 [2] || orderIsP g 3 [3] ||
    orderIsP g 4 [2] || orderIsP g 5 [5]) = true := by
  decide +kernel

theorem k5159A0 : ((((elemsC QA).drop (0 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A1 : ((((elemsC QA).drop (1 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A2 : ((((elemsC QA).drop (2 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A3 : ((((elemsC QA).drop (3 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A4 : ((((elemsC QA).drop (4 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A5 : ((((elemsC QA).drop (5 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A6 : ((((elemsC QA).drop (6 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A7 : ((((elemsC QA).drop (7 * 180)).take 180).all fun τ =>
    bif decide (τ * τ = 1 ∧ τ ≠ 1) then
      (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
       H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
     else true) = true := by
  decide +kernel

theorem k5159A : ((elemsC QA).all fun τ => bif decide (τ * τ = 1 ∧ τ ≠ 1) then
    (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
     H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
   else true) = true := by
  refine CFSG.KC.IdxChunks.all_chunks_of _ 180 8 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact k5159A0
  | 1, _ => exact k5159A1
  | 2, _ => exact k5159A2
  | 3, _ => exact k5159A3
  | 4, _ => exact k5159A4
  | 5, _ => exact k5159A5
  | 6, _ => exact k5159A6
  | 7, _ => exact k5159A7
  | k + 8, h => exact absurd h (by omega)

theorem k5159 : a6C = true := by
  unfold a6C
  rw [Bool.and_eq_true]
  exact ⟨k5159P, k5159A⟩

end CertificateChecks.KernelPermCent
