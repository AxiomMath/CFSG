module

public import CFSG.Monster.B.TwoA.Fischer.CertData
import all Init.Data.Repr
public import CFSG.Monster.B.TwoA.Fischer.CertBin

public section

namespace CertificateChecks.KernelMonB.FischerHex

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert

theorem hexDigitVal_digitChar {d : Nat} (hd : d < 16) : hexDigitVal (Nat.digitChar d) = d := by
  interval_cases d <;> decide

theorem foldl_toDigits (n : Nat) :
    (Nat.toDigits 16 n).foldl (fun acc c => acc * 16 + hexDigitVal c) 0 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by norm_num)]
    split
    · rename_i h
      simp [hexDigitVal_digitChar h]
    · rename_i h
      rw [List.foldl_append, ih (n / 16) (by omega), List.foldl_cons, List.foldl_nil,
        hexDigitVal_digitChar (Nat.mod_lt _ (by norm_num))]
      omega

theorem parseHexNat_hexStr0x (n : Nat) : parseHexNat (hexStr0x n) = n := by
  have hs : (hexStr0x n).startsWith "0x" = true := by
    simp [hexStr0x]
  unfold parseHexNat
  rw [if_pos hs, String.Slice.foldl_eq_foldl_toList, String.toList_copy_drop]
  simp only [hexStr0x, String.toList_append, String.toList_ofList]
  have h0 : "0x".toList = ['0', 'x'] := by simp
  rw [h0]
  exact foldl_toDigits n

theorem ncRowArr_eq : ncRowArr = GramLit.ncRows.toArray := by
  rw [ncRowArr]
  change ((GramLit.ncRows.map hexStr0x).map parseHexNat).toArray = _
  rw [List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id GramLit.ncRows]
  exact List.map_congr_left fun n _ => parseHexNat_hexStr0x n

end CertificateChecks.KernelMonB.FischerHex

end
