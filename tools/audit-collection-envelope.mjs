import { writeFileSync } from 'node:fs';
import { auditCollectionEnvelopeCatalog, probeCollectionReset, probeMarketOfficeResetTail, auditEpochEarnSites } from '../model/collection-envelope.mjs';
const witness = { ...auditCollectionEnvelopeCatalog(), resetProbe: probeCollectionReset(),
  marketOfficeTailProbe: probeMarketOfficeResetTail(), earnSiteAudit: auditEpochEarnSites() };
writeFileSync(new URL('../model/collection-envelope-witness.json', import.meta.url), JSON.stringify(witness, null, 2) + '\n');
console.log(JSON.stringify({ status: witness.status, catalogue: witness.facts,
  arithmeticChecks: Object.keys(witness.arithmeticChecks).length, openObligations: witness.open.length }));
