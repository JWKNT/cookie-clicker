import { describe, it } from 'mocha';
import { expect } from 'chai';

import ShortDuration from '../../src/Disp/BeautifyAndFormatting/ShortDuration.js';

describe('ShortDuration', () => {
  const examples = [
    { input: 0, output: '0s' },
    { input: 59.2, output: '1m' },
    { input: 45, output: '45s' },
    { input: 3600, output: '1h' },
    { input: 3661, output: '1h 1m' },
    { input: 2 * 86400 + 5, output: '2d' },
    { input: 9 * 86400 + 10 * 3600 + 12 * 60 + 41, output: '9d 10h' },
    { input: 400 * 86400, output: '1y 35d' },
    { input: Infinity, output: '∞' },
  ];

  examples.forEach((example) => {
    it(`Formats ${example.input} seconds as ${example.output}`, () => {
      expect(ShortDuration(example.input)).to.equal(example.output);
    });
  });
});
