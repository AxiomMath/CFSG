module

public import Certificates.Kernel.Sporadic.Fi24KPerm.Data
public import Certificates.Kernel.Sporadic.Fi24KPerm.FqA
public import Certificates.Kernel.Sporadic.Fi24KPerm.FqB
public import Certificates.Kernel.Sporadic.Fi24KPerm.FqC
public import CFSG.Certificates.Kernel.Spor.Fi24SevBSound
import CFSG.Certificates.Kernel.Common.Harness

set_option Elab.async false
set_option maxRecDepth 200000

public section

namespace CFSG.KD.Fi24KPerm.Ck

open CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24ThreeO
  CFSG.KS.Fi24Sev CFSG.KS.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem fqc_of {i : ℕ} (h0 : fqP i 0 = true) (h1 : fqP i 305530 = true) (h2 : fqP i 5604 = true)
    (h3 : fqP i 221549 = true) (h4 : fqP i 266275 = true) (h5 : fqP i 186844 = true) :
    fqc i = true := by
  unfold fqc agB
  refine allL_of fun b hb => ?_
  simp only [cb, List.mem_cons, List.not_mem_nil, or_false] at hb
  have hP : fqP i b = true := by
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  unfold fqP at hP
  rwa [ptCB_eq] at hP

theorem fqc0 : fqc (nat_lit 0) = true := fqc_of fqP0a fqP0b fqP0c fqP0d fqP0e fqP0f

theorem fqc1 : fqc (nat_lit 1) = true := fqc_of fqP1a fqP1b fqP1c fqP1d fqP1e fqP1f

theorem fqc2 : fqc (nat_lit 2) = true := fqc_of fqP2a fqP2b fqP2c fqP2d fqP2e fqP2f

theorem fqc3 : fqc (nat_lit 3) = true := fqc_of fqP3a fqP3b fqP3c fqP3d fqP3e fqP3f

theorem fqc4 : fqc (nat_lit 4) = true := fqc_of fqP4a fqP4b fqP4c fqP4d fqP4e fqP4f

theorem fqc5 : fqc (nat_lit 5) = true := fqc_of fqP5a fqP5b fqP5c fqP5d fqP5e fqP5f

theorem fqc6 : fqc (nat_lit 6) = true := fqc_of fqP6a fqP6b fqP6c fqP6d fqP6e fqP6f

theorem fqc7 : fqc (nat_lit 7) = true := fqc_of fqP7a fqP7b fqP7c fqP7d fqP7e fqP7f

theorem fqc8 : fqc (nat_lit 8) = true := fqc_of fqP8a fqP8b fqP8c fqP8d fqP8e fqP8f

theorem fqc9 : fqc (nat_lit 9) = true := fqc_of fqP9a fqP9b fqP9c fqP9d fqP9e fqP9f

theorem fqc10 : fqc (nat_lit 10) = true := fqc_of fqP10a fqP10b fqP10c fqP10d fqP10e fqP10f

theorem fqc11 : fqc (nat_lit 11) = true := fqc_of fqP11a fqP11b fqP11c fqP11d fqP11e fqP11f

theorem fqc12 : fqc (nat_lit 12) = true := fqc_of fqP12a fqP12b fqP12c fqP12d fqP12e fqP12f

theorem fqc13 : fqc (nat_lit 13) = true := fqc_of fqP13a fqP13b fqP13c fqP13d fqP13e fqP13f

theorem fqc14 : fqc (nat_lit 14) = true := fqc_of fqP14a fqP14b fqP14c fqP14d fqP14e fqP14f

theorem fqc15 : fqc (nat_lit 15) = true := fqc_of fqP15a fqP15b fqP15c fqP15d fqP15e fqP15f

theorem fqc16 : fqc (nat_lit 16) = true := fqc_of fqP16a fqP16b fqP16c fqP16d fqP16e fqP16f

theorem fqc17 : fqc (nat_lit 17) = true := fqc_of fqP17a fqP17b fqP17c fqP17d fqP17e fqP17f

theorem fqc18 : fqc (nat_lit 18) = true := fqc_of fqP18a fqP18b fqP18c fqP18d fqP18e fqP18f

theorem fqc19 : fqc (nat_lit 19) = true := fqc_of fqP19a fqP19b fqP19c fqP19d fqP19e fqP19f

theorem fqc20 : fqc (nat_lit 20) = true := fqc_of fqP20a fqP20b fqP20c fqP20d fqP20e fqP20f

theorem fqc21 : fqc (nat_lit 21) = true := fqc_of fqP21a fqP21b fqP21c fqP21d fqP21e fqP21f

theorem fqc22 : fqc (nat_lit 22) = true := fqc_of fqP22a fqP22b fqP22c fqP22d fqP22e fqP22f

theorem fqc23 : fqc (nat_lit 23) = true := fqc_of fqP23a fqP23b fqP23c fqP23d fqP23e fqP23f

theorem fqc24 : fqc (nat_lit 24) = true := fqc_of fqP24a fqP24b fqP24c fqP24d fqP24e fqP24f

theorem fqc25 : fqc (nat_lit 25) = true := fqc_of fqP25a fqP25b fqP25c fqP25d fqP25e fqP25f

theorem fqc26 : fqc (nat_lit 26) = true := fqc_of fqP26a fqP26b fqP26c fqP26d fqP26e fqP26f

theorem fqc27 : fqc (nat_lit 27) = true := fqc_of fqP27a fqP27b fqP27c fqP27d fqP27e fqP27f

theorem fqc28 : fqc (nat_lit 28) = true := fqc_of fqP28a fqP28b fqP28c fqP28d fqP28e fqP28f

theorem fqc29 : fqc (nat_lit 29) = true := fqc_of fqP29a fqP29b fqP29c fqP29d fqP29e fqP29f

theorem fqc30 : fqc (nat_lit 30) = true := fqc_of fqP30a fqP30b fqP30c fqP30d fqP30e fqP30f

theorem fqc31 : fqc (nat_lit 31) = true := fqc_of fqP31a fqP31b fqP31c fqP31d fqP31e fqP31f

theorem fqc32 : fqc (nat_lit 32) = true := fqc_of fqP32a fqP32b fqP32c fqP32d fqP32e fqP32f

theorem fqc33 : fqc (nat_lit 33) = true := fqc_of fqP33a fqP33b fqP33c fqP33d fqP33e fqP33f

theorem fqc34 : fqc (nat_lit 34) = true := fqc_of fqP34a fqP34b fqP34c fqP34d fqP34e fqP34f

theorem fqc35 : fqc (nat_lit 35) = true := fqc_of fqP35a fqP35b fqP35c fqP35d fqP35e fqP35f

theorem fqc36 : fqc (nat_lit 36) = true := fqc_of fqP36a fqP36b fqP36c fqP36d fqP36e fqP36f

theorem fqc37 : fqc (nat_lit 37) = true := fqc_of fqP37a fqP37b fqP37c fqP37d fqP37e fqP37f

theorem fqc38 : fqc (nat_lit 38) = true := fqc_of fqP38a fqP38b fqP38c fqP38d fqP38e fqP38f

theorem fqc39 : fqc (nat_lit 39) = true := fqc_of fqP39a fqP39b fqP39c fqP39d fqP39e fqP39f

theorem fqc40 : fqc (nat_lit 40) = true := fqc_of fqP40a fqP40b fqP40c fqP40d fqP40e fqP40f

theorem fqc41 : fqc (nat_lit 41) = true := fqc_of fqP41a fqP41b fqP41c fqP41d fqP41e fqP41f

theorem fqc42 : fqc (nat_lit 42) = true := fqc_of fqP42a fqP42b fqP42c fqP42d fqP42e fqP42f

theorem fqc43 : fqc (nat_lit 43) = true := fqc_of fqP43a fqP43b fqP43c fqP43d fqP43e fqP43f

theorem fqc44 : fqc (nat_lit 44) = true := fqc_of fqP44a fqP44b fqP44c fqP44d fqP44e fqP44f

theorem fqc45 : fqc (nat_lit 45) = true := fqc_of fqP45a fqP45b fqP45c fqP45d fqP45e fqP45f

theorem fqc46 : fqc (nat_lit 46) = true := fqc_of fqP46a fqP46b fqP46c fqP46d fqP46e fqP46f

theorem fqc47 : fqc (nat_lit 47) = true := fqc_of fqP47a fqP47b fqP47c fqP47d fqP47e fqP47f

theorem fqc48 : fqc (nat_lit 48) = true := fqc_of fqP48a fqP48b fqP48c fqP48d fqP48e fqP48f

theorem fqc49 : fqc (nat_lit 49) = true := fqc_of fqP49a fqP49b fqP49c fqP49d fqP49e fqP49f

theorem fqc50 : fqc (nat_lit 50) = true := fqc_of fqP50a fqP50b fqP50c fqP50d fqP50e fqP50f

theorem fqc51 : fqc (nat_lit 51) = true := fqc_of fqP51a fqP51b fqP51c fqP51d fqP51e fqP51f

theorem fqc52 : fqc (nat_lit 52) = true := fqc_of fqP52a fqP52b fqP52c fqP52d fqP52e fqP52f

theorem fqc53 : fqc (nat_lit 53) = true := fqc_of fqP53a fqP53b fqP53c fqP53d fqP53e fqP53f

theorem fqc54 : fqc (nat_lit 54) = true := fqc_of fqP54a fqP54b fqP54c fqP54d fqP54e fqP54f

theorem fqc55 : fqc (nat_lit 55) = true := fqc_of fqP55a fqP55b fqP55c fqP55d fqP55e fqP55f

theorem fqc56 : fqc (nat_lit 56) = true := fqc_of fqP56a fqP56b fqP56c fqP56d fqP56e fqP56f

theorem fqc57 : fqc (nat_lit 57) = true := fqc_of fqP57a fqP57b fqP57c fqP57d fqP57e fqP57f

theorem fqc58 : fqc (nat_lit 58) = true := fqc_of fqP58a fqP58b fqP58c fqP58d fqP58e fqP58f

theorem fqc59 : fqc (nat_lit 59) = true := fqc_of fqP59a fqP59b fqP59c fqP59d fqP59e fqP59f

theorem fqc60 : fqc (nat_lit 60) = true := fqc_of fqP60a fqP60b fqP60c fqP60d fqP60e fqP60f

theorem fqc61 : fqc (nat_lit 61) = true := fqc_of fqP61a fqP61b fqP61c fqP61d fqP61e fqP61f

theorem fqc62 : fqc (nat_lit 62) = true := fqc_of fqP62a fqP62b fqP62c fqP62d fqP62e fqP62f

theorem fqc63 : fqc (nat_lit 63) = true := fqc_of fqP63a fqP63b fqP63c fqP63d fqP63e fqP63f

theorem fqc64 : fqc (nat_lit 64) = true := fqc_of fqP64a fqP64b fqP64c fqP64d fqP64e fqP64f

theorem fqc65 : fqc (nat_lit 65) = true := fqc_of fqP65a fqP65b fqP65c fqP65d fqP65e fqP65f

theorem fqc66 : fqc (nat_lit 66) = true := fqc_of fqP66a fqP66b fqP66c fqP66d fqP66e fqP66f

theorem fqc67 : fqc (nat_lit 67) = true := fqc_of fqP67a fqP67b fqP67c fqP67d fqP67e fqP67f

theorem fqc68 : fqc (nat_lit 68) = true := fqc_of fqP68a fqP68b fqP68c fqP68d fqP68e fqP68f

theorem fNe_t : CFSG.KD.Fi24KPerm.fNe = true := by quickRfl

end CFSG.KD.Fi24KPerm.Ck

end
