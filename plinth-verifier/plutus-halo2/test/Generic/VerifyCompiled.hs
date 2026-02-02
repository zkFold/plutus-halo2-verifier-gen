{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-inline-constants #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:remove-trace #-}

module Generic.VerifyCompiled (
    verifyAppliedCompiled,
    proofMintingPolicyContractApplied,
    writeToFile,
) where

import Data.ByteString as BS
import Flat (flat)
import Generic.Proof (sampleProof)
import Plutus.Crypto.BlsTypes (Scalar)
import Plutus.Crypto.Halo2.Generic.Verifier (verify)
import PlutusCore.Version (plcVersion110)
import PlutusTx
import qualified PlutusTx.Maybe as PlutusTx
import qualified PlutusTx.Prelude as PlutusTx
import UntypedPlutusCore (DefaultFun, DefaultUni, UnrestrictedProgram (UnrestrictedProgram))

verifyAdapter :: BuiltinData -> ()
verifyAdapter proofAsData =
    let PlutusTx.Just (proof, p1) = PlutusTx.fromBuiltinData proofAsData
        (result, _) = verify proof p1
     in if result PlutusTx.== PlutusTx.True
            then ()
            else PlutusTx.error ()

verifyCompiled :: CompiledCode (BuiltinData -> ())
verifyCompiled = $$(PlutusTx.compile [||verifyAdapter||])

sampleProofCompiled :: Scalar -> CompiledCode BuiltinData
sampleProofCompiled p1 =
    let proof = PlutusTx.toBuiltinData (sampleProof, p1)
     in proof `seq` PlutusTx.liftCode plcVersion110 proof

verifyAppliedCompiled :: Scalar -> CompiledCode ()
verifyAppliedCompiled p1 =
    case verifyCompiled `applyCode` sampleProofCompiled p1 of
        Left e -> error $ show e
        Right applied -> applied

writeToFile :: Scalar -> IO ()
writeToFile p1 =
    BS.writeFile "VerifierScript.flat" . flat . UnrestrictedProgram <$> PlutusTx.getPlcNoAnn $
        (proofMintingPolicyContractApplied p1)

-- proofMintingPolicyContractApplied

-- | we are only minting here. Burning will come later
{-# INLINEABLE proofMintingContract #-}
proofMintingContract :: BuiltinData -> Bool
proofMintingContract proof =
    let PlutusTx.Just (proof', p1) = PlutusTx.fromBuiltinData proof
        (result, _) = verify proof' p1
     in result PlutusTx.== PlutusTx.True

proofMintingPolicyContractApplied ::
    Scalar ->
    CompiledCodeIn
        DefaultUni
        DefaultFun
        PlutusTx.BuiltinUnit
proofMintingPolicyContractApplied p1 =
    case $$(PlutusTx.compile [||PlutusTx.check . proofMintingContract||])
        `applyCode` (sampleProofCompiled p1) of
        Left e -> error $ show e
        Right applied -> applied
