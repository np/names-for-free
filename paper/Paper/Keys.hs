{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
module Paper.Keys where
import Kit
-- sections
[keys|intro
      overview
      termStructure
      functorSec
      monadSec
      examples
      comparison
      performance
      proofs
      discussion
      implementationExtras
      cpsSec
      closureSec
      hereditarySec
      nbeSec
      contextSec
      scopesSec
      styleSec
     |]

-- figures
-- [keys|TODO|]

-- citations
[keys|pouillard_unified_2012
      mcbride_not_2010
      chlipala_parametric_2008
      guillemette_type-preserving_2007
      guillemette_type-preserving_2008
      miller_proof_2003
      bird-paterson-99
      washburn_boxes_2003
      de_bruijn_lambda_1972
      shinwell_freshml_2003
      berger_normalization_1998
      mcbride_applicative_2007
      fegaras_revisiting_1996
      bernardy_proofs_2012
      keller_parametricity_2012
      bernardy_type-theory_2013
      bernardy_computational_2012

      de-bruijn-72 mcbride-mckinna-04 altenkirch-reus-99
      atkey-hoas-09 pouillard-pottier-10 pouillard-11
      bernardy-10 reynolds-83 mcbride-paterson-08 altenkirch-93 wadler-free-89
      bellegarde-94

      shinwell-03 pitts-06 licata-harper-09 pottier-lics-07 urban-04

      poplmark guillemette-monnier-08 elphin-05 delphin-08 delphin-09
      pientka-08 pitts-10 harper-93
      atkey-lindley-yallop-09 weirich-yorgey-sheard-11
      wadler-views-87

      taha-99 engler-96 norell-07 hutton-07 tapl attapl pottier-alphacaml
      fresh-ocaml pollack-sato-ricciotti-11 sato-pollack-10
      chargueraud-11-ln aydemir-08 cave-12

      nanevski-08
      bound-kmett-12
      namesforfreerepo
     |]

{-
alphacaml = pottieralphacaml
nominalsigs = urban04
lfcite = harper93
lncites = [chargueraud11ln, aydemir08]
spcites = [pollacksatoricciotti11, satopollack10]
-}
belugamu = cave12
fincites = [altenkirch93, mcbridemckinna04]
nestedcites = [bellegarde94, birdpaterson99, altenkirchreus99]
nbecites = [bergernormalization1998, shinwell03, pitts06, licataharper09, belugamu, pouillardunified2012]
parametricityIntegrationCites = [kellerparametricity2012, bernardycomputational2012, bernardytypetheory2013]
hereditarycites = [nanevski08] -- we could cite more

