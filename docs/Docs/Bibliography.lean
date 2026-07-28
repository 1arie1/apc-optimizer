import VersoManual

open Verso.Genre.Manual

/-! Bibliographic references, cited from `Docs.lean`. Verso renders each cite inline as
    author–year and drops the full entry in the margin. Verso's `Article` type is used for
    whitepapers and ePrint reports (`journal` carries the venue label; `volume`/`number` left
    empty). -/

namespace Docs

def powdr_autoprecompiles : Article where
  title := inlines!"Accelerating Ethereum with Autoprecompiles"
  authors := #[inlines!"powdr labs"]
  journal := inlines!"powdr labs blog"
  year := 2025
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://powdr.org/blog/accelerating-ethereum-with-autoprecompiles"

def powdr_apc_compiler : Article where
  title := inlines!"Formally Verified Autoprecompiles"
  authors := #[inlines!"powdr labs"]
  journal := inlines!"powdr labs blog"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://powdr.org/blog/formally-verified-autoprecompiles"

def powdr_wasm : Article where
  title := inlines!"powdr-wasm: an optimized zkVM for WebAssembly"
  authors := #[inlines!"powdr labs"]
  journal := inlines!"powdr labs blog"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://powdr.org/blog/powdr-wasm"

def openVM : Article where
  title := inlines!"OpenVM Whitepaper"
  authors := #[inlines!"OpenVM"]
  journal := inlines!"Whitepaper"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://openvm.dev/whitepaper.pdf"

def sp1 : Article where
  title := inlines!"SP1: a performant, open-source zkVM for RISC-V"
  authors := #[inlines!"Succinct"]
  journal := inlines!"Software, https://github.com/succinctlabs/sp1"
  year := 2024
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://github.com/succinctlabs/sp1"

def logup : Article where
  title := inlines!"Multivariate lookups based on logarithmic derivatives"
  authors := #[inlines!"Ulrich Haböck"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2022/1530"
  year := 2022
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2022/1530"

def logupGKR : Article where
  title := inlines!"Improving logarithmic derivative lookups using GKR"
  authors := #[inlines!"Shahar Papini", inlines!"Ulrich Haböck"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2023/1284"
  year := 2023
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2023/1284"

def blum : Article where
  title := inlines!"Checking the Correctness of Memories"
  authors := #[inlines!"Manuel Blum", inlines!"William S. Evans", inlines!"Peter Gemmell",
    inlines!"Sampath Kannan", inlines!"Moni Naor"]
  journal := inlines!"Algorithmica"
  year := 1994
  month := none
  volume := inlines!"12"
  number := inlines!"2"
  pages := some (225, 244)
  url := some "https://doi.org/10.1007/BF01185212"

end Docs
