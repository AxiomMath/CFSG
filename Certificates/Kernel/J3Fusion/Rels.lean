module

public import Certificates.Kernel.J3Fusion.Data
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.FusionData

public section

namespace CertificateChecks.KernelJ3Fusion

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

@[expose] noncomputable def zL (z : ℤ) : Fin 7 × Bool :=
  if 0 < z then (⟨(z - 1).toNat % 7, Nat.mod_lt _ (by decide)⟩, true)
  else (⟨(-z - 1).toNat % 7, Nat.mod_lt _ (by decide)⟩, false)

@[expose] noncomputable def pw (i : Nat) : List ℤ := pathWord (fusPaths.getD i [])

@[expose] noncomputable def invRels : List (List ℤ) :=
  (List.range 3).map fun j => fusGl.getD (j + 3) [] ++ fusGl.getD j []

@[expose] noncomputable def clRel (k : Nat) : List ℤ :=
  pw (k / 6) ++ fusGl.getD (k % 6) [] ++ invWordZ (pw (nx.getD k 0))

@[expose] noncomputable def clRels : List (List ℤ) := (List.range 768).map clRel

@[expose] noncomputable def clsRel (i : Nat) : List ℤ :=
  if cls.getD i 0 % 2 = 1 then
    fusConj.getD (cls.getD i 0 / 2) [] ++ [4] ++ invWordZ (fusConj.getD (cls.getD i 0 / 2) []) ++
      invWordZ (pw i)
  else pw i ++ pw i ++ invWordZ (pw (cls.getD i 0 / 2))

@[expose] noncomputable def clsRels : List (List ℤ) := (List.range 127).map fun i => clsRel (i + 1)

@[expose] noncomputable def relPs (rs : List (List ℤ)) : List (List (Fin 7 × Bool) × List (Fin 2 × Bool)) :=
  rs.map fun w => (w.map zL, [])

@[expose] noncomputable def pathSegs : List (List (Fin 7 × Bool)) := (List.range 128).map fun i => (pw i).map zL

@[expose] noncomputable def letOK (z : ℤ) : Bool := decide (1 ≤ z.natAbs) && decide (z.natAbs ≤ 7)

@[expose] noncomputable def dataOK : Bool :=
  fusPaths.length == 128 && nx.length == 768 && cls.length == 128 &&
    nx.all (fun q => decide (q < 128)) &&
    (List.range 127).all (fun i => cls.getD (i + 1) 0 % 2 == 1 ||
      (decide (0 < cls.getD (i + 1) 0 / 2) && decide (cls.getD (i + 1) 0 / 2 < 128))) &&
    fusPaths.getD 0 [] == [] && fusPaths.all (fun p => p.all fun j => decide (j < 6)) &&
    fusGl.all (fun g => g.all letOK) && fusConj.all (fun c => c.all letOK)

end CertificateChecks.KernelJ3Fusion

end
