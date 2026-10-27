module

public import Certificates.Kernel.GMS78.CzJChk
public import CFSG.Certificates.Kernel.GMS78RuCzJSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.CzJ

open CFSG.KC.GMS CFSG.KLie.CT CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer
  CFSG.RankThree.Native

theorem facts :
    enumOK 128 czT128 [0, 5, 3] czJCert = true ∧
      tableOK 2048 czJCert (tabOf 2048 czJCert 6) (invOf 2048 (tabOf 2048 czJCert 6))
        ((List.range 6).map (gIdx czJCert)) = true ∧
      relsHold (tabOf 2048 czJCert 6) (invOf 2048 (tabOf 2048 czJCert 6)) czRelsJ
        ((List.range 6).map (gIdx czJCert)) = true ∧
      CFSG.KC.GMS.Gen.rigidSearchG czRelsJ czWq czWw czSols 2048 (tabOf 2048 czJCert 6)
        (invOf 2048 (tabOf 2048 czJCert 6)) czJCert ((List.range 6).map (gIdx czJCert)) = true ∧
      CFSG.KC.GMS.Gen.identSearchG czRelsJ czWq czWv czWw czSols czNormX czHCodes c2JCodes
        czClass2To1 2048 (tabOf 2048 czJCert 6) (invOf 2048 (tabOf 2048 czJCert 6)) czJCert
        ((List.range 6).map (gIdx czJCert)) = true :=
  czJ_sound czT128 czT128P.toList czJCertP PT RW LK PAR LAB INV KQ KW FIX D3 D5 CT SOLS czRelsJ
    czRels1 czRels3 czRels5 czWq czWv czWw czNormX czHCodes c2JCodes HTL (czHCodes.drop 7) czSols
    czClass2To1 czT128_eq rfl rfl rfl rfl rfl t_points
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) ptB.all) t_keys t_cols t_parlab
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) rowB.all)
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) invB.all) t_prep
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) srchB.all) t_ident

theorem rigidSearch_eq (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (c : ArrCert) (gi : List ℕ) :
    rigidSearch n M inv c gi = CFSG.KC.GMS.Gen.rigidSearchG czRelsJ czWq czWw czSols n M inv c gi :=
  rfl

theorem identSearch_eq (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (c : ArrCert) (gi : List ℕ) :
    identSearch n M inv c gi = CFSG.KC.GMS.Gen.identSearchG czRelsJ czWq czWv czWw czSols czNormX
      czHCodes c2JCodes czClass2To1 n M inv c gi :=
  rfl

theorem cz_rigid : czRigidCheck = true := by
  obtain ⟨h1, h2, h3, h4, -⟩ := facts
  rw [czRigidCheck, rigidSearch_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem cz_jident : czJIdentCheck = true := by
  obtain ⟨h1, h2, -, -, h5⟩ := facts
  rw [czJIdentCheck, identSearch_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨h1, h2⟩, h5⟩

end CertificateChecks.KernelGMS78.CzJ

end
