import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkExchangeBlocks
import Physics.StandardModel.Operators.LiSixQuarkProbeDecomposition
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkExchangeBlocks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkExchangeBlocks.blocks_unique => Physics.LiSixQuarkExchangeBlocks.blocks_unique,
  GUT.LiSixQuarkExchangeBlocks.evenPart => Physics.LiSixQuarkExchangeBlocks.evenPart,
  GUT.LiSixQuarkExchangeBlocks.evenPart.eq_1 => Physics.LiSixQuarkExchangeBlocks.evenPart.eq_1,
  GUT.LiSixQuarkExchangeBlocks.even_exchange => Physics.LiSixQuarkExchangeBlocks.even_exchange,
  GUT.LiSixQuarkExchangeBlocks.even_mem_kernel => Physics.LiSixQuarkExchangeBlocks.even_mem_kernel,
  GUT.LiSixQuarkExchangeBlocks.exchange => Physics.LiSixQuarkExchangeBlocks.exchange,
  GUT.LiSixQuarkExchangeBlocks.exchange_involutive => Physics.LiSixQuarkExchangeBlocks.exchange_involutive,
  GUT.LiSixQuarkExchangeBlocks.kernel_le_iff_blocks => Physics.LiSixQuarkExchangeBlocks.kernel_le_iff_blocks,
  GUT.LiSixQuarkExchangeBlocks.oddPart => Physics.LiSixQuarkExchangeBlocks.oddPart,
  GUT.LiSixQuarkExchangeBlocks.oddPart.eq_1 => Physics.LiSixQuarkExchangeBlocks.oddPart.eq_1,
  GUT.LiSixQuarkExchangeBlocks.odd_exchange => Physics.LiSixQuarkExchangeBlocks.odd_exchange,
  GUT.LiSixQuarkExchangeBlocks.odd_mem_kernel => Physics.LiSixQuarkExchangeBlocks.odd_mem_kernel,
  GUT.LiSixQuarkExchangeBlocks.probe_exchange => Physics.LiSixQuarkExchangeBlocks.probe_exchange,
  GUT.LiSixQuarkExchangeBlocks.reconstruct => Physics.LiSixQuarkExchangeBlocks.reconstruct
]

assert_compatible GUT.LiSixQuarkExchangeBlocks.blocks_unique => Physics.LiSixQuarkExchangeBlocks.blocks_unique
assert_compatible GUT.LiSixQuarkExchangeBlocks.evenPart => Physics.LiSixQuarkExchangeBlocks.evenPart
assert_compatible GUT.LiSixQuarkExchangeBlocks.evenPart.eq_1 => Physics.LiSixQuarkExchangeBlocks.evenPart.eq_1
assert_compatible GUT.LiSixQuarkExchangeBlocks.even_exchange => Physics.LiSixQuarkExchangeBlocks.even_exchange
assert_compatible GUT.LiSixQuarkExchangeBlocks.even_mem_kernel => Physics.LiSixQuarkExchangeBlocks.even_mem_kernel
assert_compatible GUT.LiSixQuarkExchangeBlocks.exchange => Physics.LiSixQuarkExchangeBlocks.exchange
assert_compatible GUT.LiSixQuarkExchangeBlocks.exchange_involutive => Physics.LiSixQuarkExchangeBlocks.exchange_involutive
assert_compatible GUT.LiSixQuarkExchangeBlocks.kernel_le_iff_blocks => Physics.LiSixQuarkExchangeBlocks.kernel_le_iff_blocks
assert_compatible GUT.LiSixQuarkExchangeBlocks.oddPart => Physics.LiSixQuarkExchangeBlocks.oddPart
assert_compatible GUT.LiSixQuarkExchangeBlocks.oddPart.eq_1 => Physics.LiSixQuarkExchangeBlocks.oddPart.eq_1
assert_compatible GUT.LiSixQuarkExchangeBlocks.odd_exchange => Physics.LiSixQuarkExchangeBlocks.odd_exchange
assert_compatible GUT.LiSixQuarkExchangeBlocks.odd_mem_kernel => Physics.LiSixQuarkExchangeBlocks.odd_mem_kernel
assert_compatible GUT.LiSixQuarkExchangeBlocks.probe_exchange => Physics.LiSixQuarkExchangeBlocks.probe_exchange
assert_compatible GUT.LiSixQuarkExchangeBlocks.reconstruct => Physics.LiSixQuarkExchangeBlocks.reconstruct
