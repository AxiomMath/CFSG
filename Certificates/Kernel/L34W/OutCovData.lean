module

public import Certificates.Data.GrSLitL34Sec4OutCovCheck

public section

namespace CertificateChecks.KernelL34W

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.GrS4.OutCov

@[expose] def encE (x : El) : Nat := 16 * x.1 + 4 * x.2.1.val + x.2.2.val

@[expose] def maskOf (κ : ZMod 4 × ZMod 4) : Nat :=
  ((List.range 16).filter fun l => inKb κ ((l / 4 : ℕ) : ZMod 4) ((l % 4 : ℕ) : ZMod 4)).foldl
    (fun s l => s + 2 ^ l) 0

@[expose] def rhos : List Tab := [r₂T, r₃T, r₄T]

@[expose] def ocCases : Array (Nat × Nat × Nat) := Id.run do
  let mut out := #[]
  for ρi in [0:3] do
    for κi in [0:6] do
      let κ := kGensB.getD κi (0, 0)
      let ρ := rhos.getD ρi #[]
      for i₀ in [0:36] do
        if rT 0 i₀ == ρ && invar κ i₀ then
          out := out.push (κi, ρi, i₀)
  return out

@[expose] def lCodes (κ : ZMod 4 × ZMod 4) (ρ : Tab) : List Nat :=
  (liftC κ ρ).map fun x => 64 * x.2 + x.1

@[expose] def esTabs : Array Tab := (enumBFS 42 gensS 20160).tabs

@[expose] def esIdx : Std.HashMap Tab Nat := indexOf esTabs

@[expose] def caseData (c : Nat) :
    (ZMod 4 × ZMod 4) × Tab × Nat × List Nat × List Nat :=
  let e := ocCases.getD c (0, 0, 0)
  let κ := kGensB.getD e.1 (0, 0)
  let ρ := rhos.getD e.2.1 #[]
  (κ, ρ, e.2.2, fixK κ 0 e.2.2, lCodes κ ρ)

@[expose] def s3Of (c : Nat) : Array Nat :=
  let (κ, ρ, i₀, F, _) := caseData c
  let _ := κ
  ((List.range 2304).filterMap fun n =>
    let r := rT (n % 64) (n / 64)
    if commB r ρ && comp 42 r r == idTab 42 && F.all (fun k => commB r (wordTab (tg k))) then
      match esIdx.get? r with
      | some q => some (n + 8192 * q)
      | none => some (n + 4096 + 8192 * (esIdx.getD (comp 42 r ρ) 0))
    else none).toArray

@[expose] def ebOf (c : Nat) : Array Tab :=
  let (κ, ρ, i₀, _, _) := caseData c
  (enumBFS 42 (ftabs κ 0 i₀ ++ [ρ]).toArray 64).tabs

@[expose] def wAOf (c : Nat) : Nat :=
  let (κ, _, _, _, L) := caseData c
  let EB := ebOf c
  encE (((invsE κ).find? fun w => L.all fun n =>
    !inTabs EB (rT (n % 64) (n / 64)) || eqE κ (betaE (n % 64) (n / 64) w) w).getD oneE)

@[expose] def wbOf (c : Nat) : Array Nat :=
  let (κ, ρ, i₀, _, L) := caseData c
  let EB := ebOf c
  let Ft := ftabs κ 0 i₀
  (L.map fun n₁ =>
    let x₁ := rT (n₁ % 64) (n₁ / 64)
    if inTabs EB x₁ || !is2 x₁ then 0 else
      encE (((invsE κ).find? fun w => L.all fun n =>
        eqE κ (betaE (n % 64) (n / 64) w) w || !twoOK (rT (n % 64) (n / 64)) ([x₁, ρ] ++ Ft)).getD
          oneE)).toArray

@[expose] def vOf (c : Nat) : Array Nat :=
  let (κ, _, i₀, _, _) := caseData c
  (els.map fun x =>
    if eqE κ (mulE x x) oneE && eqE κ (betaE 0 i₀ x) x then
      encE ((els.find? fun v => eqE κ v (mulE (betaE 0 i₀ v) x)).getD oneE)
    else 0).toArray

@[expose] def hdrArr : Array (Array Nat) := (Array.range ocCases.size).map fun c =>
  let e := ocCases.getD c (0, 0, 0)
  let (κ, _, i₀, F, L) := caseData c
  #[64 * i₀, κ.1.val, κ.2.val, maskOf κ, F.length, L.length, wAOf c, (s3Of c).size, e.1, e.2.1]

@[expose] def fkArr : Array (Array Nat) := (Array.range ocCases.size).map fun c =>
  (caseData c).2.2.2.1.toArray

@[expose] def ftArr : Array (Array Nat) := (Array.range ocCases.size).map fun c =>
  ((caseData c).2.2.2.1.toArray.map fun k => wordTab (tg k)).flatten

@[expose] def ltArr : Array (Array Nat) := (Array.range ocCases.size).map fun c =>
  (caseData c).2.2.2.2.toArray

@[expose] def s3Arr : Array (Array Nat) := (Array.range ocCases.size).map s3Of

@[expose] def wbArr : Array (Array Nat) := (Array.range ocCases.size).map wbOf

@[expose] def vArr : Array (Array Nat) := (Array.range ocCases.size).map vOf

@[expose] def ebGens (c : Nat) : Array (Array Nat) :=
  let (κ, ρ, i₀, _, _) := caseData c
  (ftabs κ 0 i₀ ++ [ρ]).toArray

@[expose] def ebG0 : Array (Array Nat) := ebGens 0

@[expose] def ebG2 : Array (Array Nat) := ebGens 2

@[expose] def ebG4 : Array (Array Nat) := ebGens 4

@[expose] def ebG5 : Array (Array Nat) := ebGens 5

@[expose] def ebG6 : Array (Array Nat) := ebGens 6

@[expose] def kapArr : Array (Array Nat) := (List.range 6).toArray.map fun j =>
  let κ := kGensB.getD j (0, 0)
  #[κ.1.val, κ.2.val, maskOf κ,
    ((List.range 3).filter fun r => invar κ (r + 1)).foldl (fun s r => s + 2 ^ r) 0]

@[expose] def id42 : Array Nat := idTab 42

end CertificateChecks.KernelL34W

end
