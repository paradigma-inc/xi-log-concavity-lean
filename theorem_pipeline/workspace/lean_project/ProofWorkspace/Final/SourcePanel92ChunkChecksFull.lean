import ProofWorkspace.Final.SourcePanel92CheckpointsFull
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

theorem sourcePanel92Seed_checked :
    intSourceTrigSeed (ratSourcePanelCenter ⟨92, by decide⟩/40) = sourcePanel92Seed := by
  have hc : ratSourcePanelCenter ⟨92, by decide⟩/40 = (185/8000:ℚ) := by
    norm_num [ratSourcePanelCenter]
  rw [hc]
  decide +kernel

theorem sourcePanel92Checkpoint_zero :
    sourcePanel92Checkpoint 0 = (((sourceCoefficientScale:ℤ),0),List.replicate 65 0) := by
  decide +kernel

theorem sourcePanel92Chunk00_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 0 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 0
    sourceCoefficientSlice00 sourceCoefficientSlice00_checked
  decide +kernel

theorem sourcePanel92Chunk01_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 1 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 1
    sourceCoefficientSlice01 sourceCoefficientSlice01_checked
  decide +kernel

theorem sourcePanel92Chunk02_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 2 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 2
    sourceCoefficientSlice02 sourceCoefficientSlice02_checked
  decide +kernel

theorem sourcePanel92Chunk03_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 3 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 3
    sourceCoefficientSlice03 sourceCoefficientSlice03_checked
  decide +kernel

theorem sourcePanel92Chunk04_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 4 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 4
    sourceCoefficientSlice04 sourceCoefficientSlice04_checked
  decide +kernel

theorem sourcePanel92Chunk05_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 5 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 5
    sourceCoefficientSlice05 sourceCoefficientSlice05_checked
  decide +kernel

theorem sourcePanel92Chunk06_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 6 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 6
    sourceCoefficientSlice06 sourceCoefficientSlice06_checked
  decide +kernel

theorem sourcePanel92Chunk07_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 7 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 7
    sourceCoefficientSlice07 sourceCoefficientSlice07_checked
  decide +kernel

theorem sourcePanel92Chunk08_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 8 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 8
    sourceCoefficientSlice08 sourceCoefficientSlice08_checked
  decide +kernel

theorem sourcePanel92Chunk09_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 9 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 9
    sourceCoefficientSlice09 sourceCoefficientSlice09_checked
  decide +kernel

theorem sourcePanel92Chunk10_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 10 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 10
    sourceCoefficientSlice10 sourceCoefficientSlice10_checked
  decide +kernel

theorem sourcePanel92Chunk11_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 11 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 11
    sourceCoefficientSlice11 sourceCoefficientSlice11_checked
  decide +kernel

theorem sourcePanel92Chunk12_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 12 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 12
    sourceCoefficientSlice12 sourceCoefficientSlice12_checked
  decide +kernel

theorem sourcePanel92Chunk13_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 13 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 13
    sourceCoefficientSlice13 sourceCoefficientSlice13_checked
  decide +kernel

theorem sourcePanel92Chunk14_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 14 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 14
    sourceCoefficientSlice14 sourceCoefficientSlice14_checked
  decide +kernel

theorem sourcePanel92Chunk15_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 15 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 15
    sourceCoefficientSlice15 sourceCoefficientSlice15_checked
  decide +kernel

theorem sourcePanel92Chunk16_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 16 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 16
    sourceCoefficientSlice16 sourceCoefficientSlice16_checked
  decide +kernel

theorem sourcePanel92Chunk17_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 17 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 17
    sourceCoefficientSlice17 sourceCoefficientSlice17_checked
  decide +kernel

theorem sourcePanel92Chunk18_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 18 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 18
    sourceCoefficientSlice18 sourceCoefficientSlice18_checked
  decide +kernel

theorem sourcePanel92Chunk19_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 19 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 19
    sourceCoefficientSlice19 sourceCoefficientSlice19_checked
  decide +kernel

theorem sourcePanel92Chunk20_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 20 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 20
    sourceCoefficientSlice20 sourceCoefficientSlice20_checked
  decide +kernel

theorem sourcePanel92Chunk21_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 21 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 21
    sourceCoefficientSlice21 sourceCoefficientSlice21_checked
  decide +kernel

theorem sourcePanel92Chunk22_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 22 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 22
    sourceCoefficientSlice22 sourceCoefficientSlice22_checked
  decide +kernel

theorem sourcePanel92Chunk23_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 23 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 23
    sourceCoefficientSlice23 sourceCoefficientSlice23_checked
  decide +kernel

theorem sourcePanel92Chunk24_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 24 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 24
    sourceCoefficientSlice24 sourceCoefficientSlice24_checked
  decide +kernel

theorem sourcePanel92Chunk25_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 25 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 25
    sourceCoefficientSlice25 sourceCoefficientSlice25_checked
  decide +kernel

theorem sourcePanel92Chunk26_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 26 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 26
    sourceCoefficientSlice26 sourceCoefficientSlice26_checked
  decide +kernel

theorem sourcePanel92Chunk27_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 27 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 27
    sourceCoefficientSlice27 sourceCoefficientSlice27_checked
  decide +kernel

theorem sourcePanel92Chunk28_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 28 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 28
    sourceCoefficientSlice28 sourceCoefficientSlice28_checked
  decide +kernel

theorem sourcePanel92Chunk29_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 29 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 29
    sourceCoefficientSlice29 sourceCoefficientSlice29_checked
  decide +kernel

theorem sourcePanel92Chunk30_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 30 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 30
    sourceCoefficientSlice30 sourceCoefficientSlice30_checked
  decide +kernel

theorem sourcePanel92Chunk31_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 31 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 31
    sourceCoefficientSlice31 sourceCoefficientSlice31_checked
  decide +kernel

theorem sourcePanel92Chunk32_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 32 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 32
    sourceCoefficientSlice32 sourceCoefficientSlice32_checked
  decide +kernel

theorem sourcePanel92Chunk33_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 33 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 33
    sourceCoefficientSlice33 sourceCoefficientSlice33_checked
  decide +kernel

theorem sourcePanel92Chunk34_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 34 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 34
    sourceCoefficientSlice34 sourceCoefficientSlice34_checked
  decide +kernel

theorem sourcePanel92Chunk35_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 35 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 35
    sourceCoefficientSlice35 sourceCoefficientSlice35_checked
  decide +kernel

theorem sourcePanel92Chunk36_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 36 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 36
    sourceCoefficientSlice36 sourceCoefficientSlice36_checked
  decide +kernel

theorem sourcePanel92Chunk37_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 37 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 37
    sourceCoefficientSlice37 sourceCoefficientSlice37_checked
  decide +kernel

theorem sourcePanel92Chunk38_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 38 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 38
    sourceCoefficientSlice38 sourceCoefficientSlice38_checked
  decide +kernel

theorem sourcePanel92Chunk39_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 39 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 39
    sourceCoefficientSlice39 sourceCoefficientSlice39_checked
  decide +kernel

theorem sourcePanel92Chunk40_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 40 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 40
    sourceCoefficientSlice40 sourceCoefficientSlice40_checked
  decide +kernel

theorem sourcePanel92Chunk41_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 41 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 41
    sourceCoefficientSlice41 sourceCoefficientSlice41_checked
  decide +kernel

theorem sourcePanel92Chunk42_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 42 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 42
    sourceCoefficientSlice42 sourceCoefficientSlice42_checked
  decide +kernel

theorem sourcePanel92Chunk43_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 43 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 43
    sourceCoefficientSlice43 sourceCoefficientSlice43_checked
  decide +kernel

theorem sourcePanel92Chunk44_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 44 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 44
    sourceCoefficientSlice44 sourceCoefficientSlice44_checked
  decide +kernel

theorem sourcePanel92Chunk45_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 45 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 45
    sourceCoefficientSlice45 sourceCoefficientSlice45_checked
  decide +kernel

theorem sourcePanel92Chunk46_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 46 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 46
    sourceCoefficientSlice46 sourceCoefficientSlice46_checked
  decide +kernel

theorem sourcePanel92Chunk47_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 47 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 47
    sourceCoefficientSlice47 sourceCoefficientSlice47_checked
  decide +kernel

theorem sourcePanel92Chunk48_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 48 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 48
    sourceCoefficientSlice48 sourceCoefficientSlice48_checked
  decide +kernel

theorem sourcePanel92Chunk49_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 49 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 49
    sourceCoefficientSlice49 sourceCoefficientSlice49_checked
  decide +kernel

theorem sourcePanel92Chunk50_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 50 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 50
    sourceCoefficientSlice50 sourceCoefficientSlice50_checked
  decide +kernel

theorem sourcePanel92Chunk51_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 51 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 51
    sourceCoefficientSlice51 sourceCoefficientSlice51_checked
  decide +kernel

theorem sourcePanel92Chunk52_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 52 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 52
    sourceCoefficientSlice52 sourceCoefficientSlice52_checked
  decide +kernel

theorem sourcePanel92Chunk53_checked :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint 53 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel92Seed sourcePanel92Checkpoint 53
    sourceCoefficientSlice53 sourceCoefficientSlice53_checked
  decide +kernel

theorem sourcePanel92Chunks_checked (i : Fin 54) :
    sourcePanelChunkCheck sourcePanel92Seed sourcePanel92Checkpoint i := by
  fin_cases i
  · exact sourcePanel92Chunk00_checked
  · exact sourcePanel92Chunk01_checked
  · exact sourcePanel92Chunk02_checked
  · exact sourcePanel92Chunk03_checked
  · exact sourcePanel92Chunk04_checked
  · exact sourcePanel92Chunk05_checked
  · exact sourcePanel92Chunk06_checked
  · exact sourcePanel92Chunk07_checked
  · exact sourcePanel92Chunk08_checked
  · exact sourcePanel92Chunk09_checked
  · exact sourcePanel92Chunk10_checked
  · exact sourcePanel92Chunk11_checked
  · exact sourcePanel92Chunk12_checked
  · exact sourcePanel92Chunk13_checked
  · exact sourcePanel92Chunk14_checked
  · exact sourcePanel92Chunk15_checked
  · exact sourcePanel92Chunk16_checked
  · exact sourcePanel92Chunk17_checked
  · exact sourcePanel92Chunk18_checked
  · exact sourcePanel92Chunk19_checked
  · exact sourcePanel92Chunk20_checked
  · exact sourcePanel92Chunk21_checked
  · exact sourcePanel92Chunk22_checked
  · exact sourcePanel92Chunk23_checked
  · exact sourcePanel92Chunk24_checked
  · exact sourcePanel92Chunk25_checked
  · exact sourcePanel92Chunk26_checked
  · exact sourcePanel92Chunk27_checked
  · exact sourcePanel92Chunk28_checked
  · exact sourcePanel92Chunk29_checked
  · exact sourcePanel92Chunk30_checked
  · exact sourcePanel92Chunk31_checked
  · exact sourcePanel92Chunk32_checked
  · exact sourcePanel92Chunk33_checked
  · exact sourcePanel92Chunk34_checked
  · exact sourcePanel92Chunk35_checked
  · exact sourcePanel92Chunk36_checked
  · exact sourcePanel92Chunk37_checked
  · exact sourcePanel92Chunk38_checked
  · exact sourcePanel92Chunk39_checked
  · exact sourcePanel92Chunk40_checked
  · exact sourcePanel92Chunk41_checked
  · exact sourcePanel92Chunk42_checked
  · exact sourcePanel92Chunk43_checked
  · exact sourcePanel92Chunk44_checked
  · exact sourcePanel92Chunk45_checked
  · exact sourcePanel92Chunk46_checked
  · exact sourcePanel92Chunk47_checked
  · exact sourcePanel92Chunk48_checked
  · exact sourcePanel92Chunk49_checked
  · exact sourcePanel92Chunk50_checked
  · exact sourcePanel92Chunk51_checked
  · exact sourcePanel92Chunk52_checked
  · exact sourcePanel92Chunk53_checked

end ReciprocalXi
