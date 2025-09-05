import { CREUSOT_TYPES, LITERALS, PEARLITE_KEYWORDS, TYPES, utils } from './rust.js';

export default function(hljs) {
  const UTILS = utils(hljs);
  const PEARLITE = UTILS.pearlite;
  return {
    name: 'Pearlite',
    aliases: [],
    literals: LITERALS,
    keywords: {
      keyword: PEARLITE_KEYWORDS,
      type: TYPES,
      'creusot-type': CREUSOT_TYPES,
    },
    contains: PEARLITE,
  }
}
