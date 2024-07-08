module ZkFold.Base.Protocol.ARK.Protostar where

{--

1. Compress verification checks (Section 3.5; )
2. Commit (Section 3.2; ZkFold.Base.Protocol.ARK.Protostar.CommitOpen)
3. Fiat-Shamir transform (Section 3.3; ZkFold.Base.Protocol.ARK.Protostar.FiatShamir)
   A technique for taking an interactive proof of knowledge and creating a digital signature based on it. 
   This way, some fact (for example, knowledge of a certain secret number) can be publicly proven without revealing underlying information.
4. Accumulation scheme (Section 3.4; ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme)
5. Obtain the IVC scheme (Theorem 1 from “Proof-Carrying Data Without Succinct Arguments”; )

--}
--
-- TODO: is 1. mandatory?
-- How is Protostar related to ArithmeticCircuits?
-- Only PlonkUP is mentioned in the paper, can we implement it with the regular Plonk?
-- yes, w/o lookups
--
--
-- To complete the protocol:
-- 1. Finish AccumulatorScheme -- and Lookup
-- 2. Implement IVC scheme
-- 3. Put it all together
-- 4. Input and output == AC
