import ProofWorkspace.Final.SourcePanel99CheckpointsFull
import ProofWorkspace.Final.SourceCoefficientSlice00Full
import ProofWorkspace.Final.SourceCoefficientSlice01Full
import ProofWorkspace.Final.SourceCoefficientSlice02Full
import ProofWorkspace.Final.SourceCoefficientSlice03Full
import ProofWorkspace.Final.SourceCoefficientSlice04Full
import ProofWorkspace.Final.SourceCoefficientSlice05Full
import ProofWorkspace.Final.SourceCoefficientSlice06Full
import ProofWorkspace.Final.SourceCoefficientSlice07Full
import ProofWorkspace.Final.SourceCoefficientSlice08Full
import ProofWorkspace.Final.SourceCoefficientSlice09Full
import ProofWorkspace.Final.SourceCoefficientSlice10Full
import ProofWorkspace.Final.SourceCoefficientSlice11Full
import ProofWorkspace.Final.SourceCoefficientSlice12Full
import ProofWorkspace.Final.SourceCoefficientSlice13Full
import ProofWorkspace.Final.SourceCoefficientSlice14Full
import ProofWorkspace.Final.SourceCoefficientSlice15Full
import ProofWorkspace.Final.SourceCoefficientSlice16Full
import ProofWorkspace.Final.SourceCoefficientSlice17Full
import ProofWorkspace.Final.SourceCoefficientSlice18Full
import ProofWorkspace.Final.SourceCoefficientSlice19Full
import ProofWorkspace.Final.SourceCoefficientSlice20Full
import ProofWorkspace.Final.SourceCoefficientSlice21Full
import ProofWorkspace.Final.SourceCoefficientSlice22Full
import ProofWorkspace.Final.SourceCoefficientSlice23Full
import ProofWorkspace.Final.SourceCoefficientSlice24Full
import ProofWorkspace.Final.SourceCoefficientSlice25Full
import ProofWorkspace.Final.SourceCoefficientSlice26Full
import ProofWorkspace.Final.SourceCoefficientSlice27Full
import ProofWorkspace.Final.SourceCoefficientSlice28Full
import ProofWorkspace.Final.SourceCoefficientSlice29Full
import ProofWorkspace.Final.SourceCoefficientSlice30Full
import ProofWorkspace.Final.SourceCoefficientSlice31Full
import ProofWorkspace.Final.SourceCoefficientSlice32Full
import ProofWorkspace.Final.SourceCoefficientSlice33Full
import ProofWorkspace.Final.SourceCoefficientSlice34Full
import ProofWorkspace.Final.SourceCoefficientSlice35Full
import ProofWorkspace.Final.SourceCoefficientSlice36Full
import ProofWorkspace.Final.SourceCoefficientSlice37Full
import ProofWorkspace.Final.SourceCoefficientSlice38Full
import ProofWorkspace.Final.SourceCoefficientSlice39Full
import ProofWorkspace.Final.SourceCoefficientSlice40Full
import ProofWorkspace.Final.SourceCoefficientSlice41Full
import ProofWorkspace.Final.SourceCoefficientSlice42Full
import ProofWorkspace.Final.SourceCoefficientSlice43Full
import ProofWorkspace.Final.SourceCoefficientSlice44Full
import ProofWorkspace.Final.SourceCoefficientSlice45Full
import ProofWorkspace.Final.SourceCoefficientSlice46Full
import ProofWorkspace.Final.SourceCoefficientSlice47Full
import ProofWorkspace.Final.SourceCoefficientSlice48Full
import ProofWorkspace.Final.SourceCoefficientSlice49Full
import ProofWorkspace.Final.SourceCoefficientSlice50Full
import ProofWorkspace.Final.SourceCoefficientSlice51Full
import ProofWorkspace.Final.SourceCoefficientSlice52Full
import ProofWorkspace.Final.SourceCoefficientSlice53Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel99Seed_checked :
    intSourceTrigSeed (ratSourcePanelCenter ⟨99, by decide⟩/40) = sourcePanel99Seed := by
  have hc : ratSourcePanelCenter ⟨99, by decide⟩/40 = (199/8000:ℚ) := by
    norm_num [ratSourcePanelCenter]
  rw [hc]
  decide +kernel

theorem sourcePanel99Checkpoint_zero :
    sourcePanel99Checkpoint 0 = (((sourceCoefficientScale:ℤ),0),List.replicate 65 0) := by
  decide +kernel

theorem sourcePanel99Chunk00_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 0 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 0
    sourceCoefficientSlice00 sourceCoefficientSlice00_checked
  decide +kernel

theorem sourcePanel99Chunk01_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 1 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 1
    sourceCoefficientSlice01 sourceCoefficientSlice01_checked
  decide +kernel

theorem sourcePanel99Chunk02_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 2 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 2
    sourceCoefficientSlice02 sourceCoefficientSlice02_checked
  decide +kernel

theorem sourcePanel99Chunk03_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 3 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 3
    sourceCoefficientSlice03 sourceCoefficientSlice03_checked
  decide +kernel

theorem sourcePanel99Chunk04_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 4 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 4
    sourceCoefficientSlice04 sourceCoefficientSlice04_checked
  decide +kernel

theorem sourcePanel99Chunk05_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 5 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 5
    sourceCoefficientSlice05 sourceCoefficientSlice05_checked
  decide +kernel

theorem sourcePanel99Chunk06_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 6 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 6
    sourceCoefficientSlice06 sourceCoefficientSlice06_checked
  decide +kernel

theorem sourcePanel99Chunk07_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 7 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 7
    sourceCoefficientSlice07 sourceCoefficientSlice07_checked
  decide +kernel

theorem sourcePanel99Chunk08_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 8 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 8
    sourceCoefficientSlice08 sourceCoefficientSlice08_checked
  decide +kernel

theorem sourcePanel99Chunk09_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 9 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 9
    sourceCoefficientSlice09 sourceCoefficientSlice09_checked
  decide +kernel

theorem sourcePanel99Chunk10_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 10 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 10
    sourceCoefficientSlice10 sourceCoefficientSlice10_checked
  decide +kernel

theorem sourcePanel99Chunk11_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 11 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 11
    sourceCoefficientSlice11 sourceCoefficientSlice11_checked
  decide +kernel

theorem sourcePanel99Chunk12_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 12 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 12
    sourceCoefficientSlice12 sourceCoefficientSlice12_checked
  decide +kernel

theorem sourcePanel99Chunk13_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 13 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 13
    sourceCoefficientSlice13 sourceCoefficientSlice13_checked
  decide +kernel

theorem sourcePanel99Chunk14_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 14 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 14
    sourceCoefficientSlice14 sourceCoefficientSlice14_checked
  decide +kernel

theorem sourcePanel99Chunk15_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 15 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 15
    sourceCoefficientSlice15 sourceCoefficientSlice15_checked
  decide +kernel

theorem sourcePanel99Chunk16_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 16 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 16
    sourceCoefficientSlice16 sourceCoefficientSlice16_checked
  decide +kernel

theorem sourcePanel99Chunk17_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 17 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 17
    sourceCoefficientSlice17 sourceCoefficientSlice17_checked
  decide +kernel

theorem sourcePanel99Chunk18_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 18 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 18
    sourceCoefficientSlice18 sourceCoefficientSlice18_checked
  decide +kernel

theorem sourcePanel99Chunk19_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 19 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 19
    sourceCoefficientSlice19 sourceCoefficientSlice19_checked
  decide +kernel

theorem sourcePanel99Chunk20_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 20 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 20
    sourceCoefficientSlice20 sourceCoefficientSlice20_checked
  decide +kernel

theorem sourcePanel99Chunk21_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 21 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 21
    sourceCoefficientSlice21 sourceCoefficientSlice21_checked
  decide +kernel

theorem sourcePanel99Chunk22_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 22 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 22
    sourceCoefficientSlice22 sourceCoefficientSlice22_checked
  decide +kernel

theorem sourcePanel99Chunk23_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 23 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 23
    sourceCoefficientSlice23 sourceCoefficientSlice23_checked
  decide +kernel

theorem sourcePanel99Chunk24_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 24 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 24
    sourceCoefficientSlice24 sourceCoefficientSlice24_checked
  decide +kernel

theorem sourcePanel99Chunk25_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 25 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 25
    sourceCoefficientSlice25 sourceCoefficientSlice25_checked
  decide +kernel

theorem sourcePanel99Chunk26_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 26 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 26
    sourceCoefficientSlice26 sourceCoefficientSlice26_checked
  decide +kernel

theorem sourcePanel99Chunk27_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 27 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 27
    sourceCoefficientSlice27 sourceCoefficientSlice27_checked
  decide +kernel

theorem sourcePanel99Chunk28_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 28 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 28
    sourceCoefficientSlice28 sourceCoefficientSlice28_checked
  decide +kernel

theorem sourcePanel99Chunk29_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 29 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 29
    sourceCoefficientSlice29 sourceCoefficientSlice29_checked
  decide +kernel

theorem sourcePanel99Chunk30_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 30 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 30
    sourceCoefficientSlice30 sourceCoefficientSlice30_checked
  decide +kernel

theorem sourcePanel99Chunk31_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 31 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 31
    sourceCoefficientSlice31 sourceCoefficientSlice31_checked
  decide +kernel

theorem sourcePanel99Chunk32_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 32 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 32
    sourceCoefficientSlice32 sourceCoefficientSlice32_checked
  decide +kernel

theorem sourcePanel99Chunk33_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 33 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 33
    sourceCoefficientSlice33 sourceCoefficientSlice33_checked
  decide +kernel

theorem sourcePanel99Chunk34_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 34 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 34
    sourceCoefficientSlice34 sourceCoefficientSlice34_checked
  decide +kernel

theorem sourcePanel99Chunk35_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 35 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 35
    sourceCoefficientSlice35 sourceCoefficientSlice35_checked
  decide +kernel

theorem sourcePanel99Chunk36_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 36 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 36
    sourceCoefficientSlice36 sourceCoefficientSlice36_checked
  decide +kernel

theorem sourcePanel99Chunk37_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 37 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 37
    sourceCoefficientSlice37 sourceCoefficientSlice37_checked
  decide +kernel

theorem sourcePanel99Chunk38_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 38 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 38
    sourceCoefficientSlice38 sourceCoefficientSlice38_checked
  decide +kernel

theorem sourcePanel99Chunk39_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 39 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 39
    sourceCoefficientSlice39 sourceCoefficientSlice39_checked
  decide +kernel

theorem sourcePanel99Chunk40_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 40 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 40
    sourceCoefficientSlice40 sourceCoefficientSlice40_checked
  decide +kernel

theorem sourcePanel99Chunk41_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 41 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 41
    sourceCoefficientSlice41 sourceCoefficientSlice41_checked
  decide +kernel

theorem sourcePanel99Chunk42_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 42 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 42
    sourceCoefficientSlice42 sourceCoefficientSlice42_checked
  decide +kernel

theorem sourcePanel99Chunk43_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 43 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 43
    sourceCoefficientSlice43 sourceCoefficientSlice43_checked
  decide +kernel

theorem sourcePanel99Chunk44_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 44 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 44
    sourceCoefficientSlice44 sourceCoefficientSlice44_checked
  decide +kernel

theorem sourcePanel99Chunk45_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 45 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 45
    sourceCoefficientSlice45 sourceCoefficientSlice45_checked
  decide +kernel

theorem sourcePanel99Chunk46_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 46 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 46
    sourceCoefficientSlice46 sourceCoefficientSlice46_checked
  decide +kernel

theorem sourcePanel99Chunk47_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 47 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 47
    sourceCoefficientSlice47 sourceCoefficientSlice47_checked
  decide +kernel

theorem sourcePanel99Chunk48_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 48 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 48
    sourceCoefficientSlice48 sourceCoefficientSlice48_checked
  decide +kernel

theorem sourcePanel99Chunk49_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 49 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 49
    sourceCoefficientSlice49 sourceCoefficientSlice49_checked
  decide +kernel

theorem sourcePanel99Chunk50_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 50 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 50
    sourceCoefficientSlice50 sourceCoefficientSlice50_checked
  decide +kernel

theorem sourcePanel99Chunk51_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 51 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 51
    sourceCoefficientSlice51 sourceCoefficientSlice51_checked
  decide +kernel

theorem sourcePanel99Chunk52_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 52 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 52
    sourceCoefficientSlice52 sourceCoefficientSlice52_checked
  decide +kernel

theorem sourcePanel99Chunk53_checked :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint 53 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel99Seed sourcePanel99Checkpoint 53
    sourceCoefficientSlice53 sourceCoefficientSlice53_checked
  decide +kernel

theorem sourcePanel99Chunks_checked (i : Fin 54) :
    sourcePanelChunkCheck sourcePanel99Seed sourcePanel99Checkpoint i := by
  fin_cases i
  · exact sourcePanel99Chunk00_checked
  · exact sourcePanel99Chunk01_checked
  · exact sourcePanel99Chunk02_checked
  · exact sourcePanel99Chunk03_checked
  · exact sourcePanel99Chunk04_checked
  · exact sourcePanel99Chunk05_checked
  · exact sourcePanel99Chunk06_checked
  · exact sourcePanel99Chunk07_checked
  · exact sourcePanel99Chunk08_checked
  · exact sourcePanel99Chunk09_checked
  · exact sourcePanel99Chunk10_checked
  · exact sourcePanel99Chunk11_checked
  · exact sourcePanel99Chunk12_checked
  · exact sourcePanel99Chunk13_checked
  · exact sourcePanel99Chunk14_checked
  · exact sourcePanel99Chunk15_checked
  · exact sourcePanel99Chunk16_checked
  · exact sourcePanel99Chunk17_checked
  · exact sourcePanel99Chunk18_checked
  · exact sourcePanel99Chunk19_checked
  · exact sourcePanel99Chunk20_checked
  · exact sourcePanel99Chunk21_checked
  · exact sourcePanel99Chunk22_checked
  · exact sourcePanel99Chunk23_checked
  · exact sourcePanel99Chunk24_checked
  · exact sourcePanel99Chunk25_checked
  · exact sourcePanel99Chunk26_checked
  · exact sourcePanel99Chunk27_checked
  · exact sourcePanel99Chunk28_checked
  · exact sourcePanel99Chunk29_checked
  · exact sourcePanel99Chunk30_checked
  · exact sourcePanel99Chunk31_checked
  · exact sourcePanel99Chunk32_checked
  · exact sourcePanel99Chunk33_checked
  · exact sourcePanel99Chunk34_checked
  · exact sourcePanel99Chunk35_checked
  · exact sourcePanel99Chunk36_checked
  · exact sourcePanel99Chunk37_checked
  · exact sourcePanel99Chunk38_checked
  · exact sourcePanel99Chunk39_checked
  · exact sourcePanel99Chunk40_checked
  · exact sourcePanel99Chunk41_checked
  · exact sourcePanel99Chunk42_checked
  · exact sourcePanel99Chunk43_checked
  · exact sourcePanel99Chunk44_checked
  · exact sourcePanel99Chunk45_checked
  · exact sourcePanel99Chunk46_checked
  · exact sourcePanel99Chunk47_checked
  · exact sourcePanel99Chunk48_checked
  · exact sourcePanel99Chunk49_checked
  · exact sourcePanel99Chunk50_checked
  · exact sourcePanel99Chunk51_checked
  · exact sourcePanel99Chunk52_checked
  · exact sourcePanel99Chunk53_checked

end ReciprocalXi
