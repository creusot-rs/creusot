/*!
  Highlight.js v11.11.1 (git: cf688ee195)
  (c) 2006-2025 Josh Goebel <hello@joshgoebel.com> and other contributors
  License: BSD-3-Clause
 */
var hljs=function(){"use strict";function e(t){
return t instanceof Map?t.clear=t.delete=t.set=()=>{
throw Error("map is read-only")}:t instanceof Set&&(t.add=t.clear=t.delete=()=>{
throw Error("set is read-only")
}),Object.freeze(t),Object.getOwnPropertyNames(t).forEach((n=>{
const i=t[n],s=typeof i;"object"!==s&&"function"!==s||Object.isFrozen(i)||e(i)
})),t}class t{constructor(e){
void 0===e.data&&(e.data={}),this.data=e.data,this.isMatchIgnored=!1}
ignoreMatch(){this.isMatchIgnored=!0}}function n(e){
return e.replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;").replace(/"/g,"&quot;").replace(/'/g,"&#x27;")
}function i(e,...t){const n=Object.create(null);for(const t in e)n[t]=e[t]
;return t.forEach((e=>{for(const t in e)n[t]=e[t]})),n}const s=e=>!!e.scope
;class r{constructor(e,t){
this.buffer="",this.classPrefix=t.classPrefix,e.walk(this)}addText(e){
this.buffer+=n(e)}openNode(e){if(!s(e))return;const t=((e,{prefix:t})=>{
if(e.startsWith("language:"))return e.replace("language:","language-")
;if(e.includes(".")){const n=e.split(".")
;return[`${t}${n.shift()}`,...n.map(((e,t)=>`${e}${"_".repeat(t+1)}`))].join(" ")
}return`${t}${e}`})(e.scope,{prefix:this.classPrefix});this.span(t)}
closeNode(e){s(e)&&(this.buffer+="</span>")}value(){return this.buffer}span(e){
this.buffer+=`<span class="${e}">`}}const o=(e={})=>{const t={children:[]}
;return Object.assign(t,e),t};class a{constructor(){
this.rootNode=o(),this.stack=[this.rootNode]}get top(){
return this.stack[this.stack.length-1]}get root(){return this.rootNode}add(e){
this.top.children.push(e)}openNode(e){const t=o({scope:e})
;this.add(t),this.stack.push(t)}closeNode(){
if(this.stack.length>1)return this.stack.pop()}closeAllNodes(){
for(;this.closeNode(););}toJSON(){return JSON.stringify(this.rootNode,null,4)}
walk(e){return this.constructor._walk(e,this.rootNode)}static _walk(e,t){
return"string"==typeof t?e.addText(t):t.children&&(e.openNode(t),
t.children.forEach((t=>this._walk(e,t))),e.closeNode(t)),e}static _collapse(e){
"string"!=typeof e&&e.children&&(e.children.every((e=>"string"==typeof e))?e.children=[e.children.join("")]:e.children.forEach((e=>{
a._collapse(e)})))}}class c extends a{constructor(e){super(),this.options=e}
addText(e){""!==e&&this.add(e)}startScope(e){this.openNode(e)}endScope(){
this.closeNode()}__addSublanguage(e,t){const n=e.root
;t&&(n.scope="language:"+t),this.add(n)}toHTML(){
return new r(this,this.options).value()}finalize(){
return this.closeAllNodes(),!0}}function l(e){
return e?"string"==typeof e?e:e.source:null}function g(e){return h("(?=",e,")")}
function u(e){return h("(?:",e,")*")}function d(e){return h("(?:",e,")?")}
function h(...e){return e.map((e=>l(e))).join("")}function p(...e){const t=(e=>{
const t=e[e.length-1]
;return"object"==typeof t&&t.constructor===Object?(e.splice(e.length-1,1),t):{}
})(e);return"("+(t.capture?"":"?:")+e.map((e=>l(e))).join("|")+")"}
function f(e){return RegExp(e.toString()+"|").exec("").length-1}
const b=/\[(?:[^\\\]]|\\.)*\]|\(\??|\\([1-9][0-9]*)|\\./
;function m(e,{joinWith:t}){let n=0;return e.map((e=>{n+=1;const t=n
;let i=l(e),s="";for(;i.length>0;){const e=b.exec(i);if(!e){s+=i;break}
s+=i.substring(0,e.index),
i=i.substring(e.index+e[0].length),"\\"===e[0][0]&&e[1]?s+="\\"+(Number(e[1])+t):(s+=e[0],
"("===e[0]&&n++)}return s})).map((e=>`(${e})`)).join(t)}
const _="[a-zA-Z]\\w*",E="[a-zA-Z_]\\w*",y="\\b\\d+(\\.\\d+)?",w="(-?)(\\b0[xX][a-fA-F0-9]+|(\\b\\d+(\\.\\d*)?|\\.\\d+)([eE][-+]?\\d+)?)",x="\\b(0b[01]+)",k={
begin:"\\\\[\\s\\S]",relevance:0},N={scope:"string",begin:"'",end:"'",
illegal:"\\n",contains:[k]},v={scope:"string",begin:'"',end:'"',illegal:"\\n",
contains:[k]},O=(e,t,n={})=>{const s=i({scope:"comment",begin:e,end:t,
contains:[]},n);s.contains.push({scope:"doctag",
begin:"[ ]*(?=(TODO|FIXME|NOTE|BUG|OPTIMIZE|HACK|XXX):)",
end:/(TODO|FIXME|NOTE|BUG|OPTIMIZE|HACK|XXX):/,excludeBegin:!0,relevance:0})
;const r=p("I","a","is","so","us","to","at","if","in","it","on",/[A-Za-z]+['](d|ve|re|ll|t|s|n)/,/[A-Za-z]+[-][a-z]+/,/[A-Za-z][a-z]{2,}/)
;return s.contains.push({begin:h(/[ ]+/,"(",r,/[.]?[:]?([.][ ]|[ ])/,"){3}")}),s
},S=O("//","$"),M=O("/\\*","\\*/"),R=O("#","$");var I=Object.freeze({
__proto__:null,APOS_STRING_MODE:N,BACKSLASH_ESCAPE:k,BINARY_NUMBER_MODE:{
scope:"number",begin:x,relevance:0},BINARY_NUMBER_RE:x,COMMENT:O,
C_BLOCK_COMMENT_MODE:M,C_LINE_COMMENT_MODE:S,C_NUMBER_MODE:{scope:"number",
begin:w,relevance:0},C_NUMBER_RE:w,END_SAME_AS_BEGIN:e=>Object.assign(e,{
"on:begin":(e,t)=>{t.data._beginMatch=e[1]},"on:end":(e,t)=>{
t.data._beginMatch!==e[1]&&t.ignoreMatch()}}),HASH_COMMENT_MODE:R,IDENT_RE:_,
MATCH_NOTHING_RE:/\b\B/,METHOD_GUARD:{begin:"\\.\\s*"+E,relevance:0},
NUMBER_MODE:{scope:"number",begin:y,relevance:0},NUMBER_RE:y,
PHRASAL_WORDS_MODE:{
begin:/\b(a|an|the|are|I'm|isn't|don't|doesn't|won't|but|just|should|pretty|simply|enough|gonna|going|wtf|so|such|will|you|your|they|like|more)\b/
},QUOTE_STRING_MODE:v,REGEXP_MODE:{scope:"regexp",begin:/\/(?=[^/\n]*\/)/,
end:/\/[gimuy]*/,contains:[k,{begin:/\[/,end:/\]/,relevance:0,contains:[k]}]},
RE_STARTERS_RE:"!|!=|!==|%|%=|&|&&|&=|\\*|\\*=|\\+|\\+=|,|-|-=|/=|/|:|;|<<|<<=|<=|<|===|==|=|>>>=|>>=|>=|>>>|>>|>|\\?|\\[|\\{|\\(|\\^|\\^=|\\||\\|=|\\|\\||~",
SHEBANG:(e={})=>{const t=/^#![ ]*\//
;return e.binary&&(e.begin=h(t,/.*\b/,e.binary,/\b.*/)),i({scope:"meta",begin:t,
end:/$/,relevance:0,"on:begin":(e,t)=>{0!==e.index&&t.ignoreMatch()}},e)},
TITLE_MODE:{scope:"title",begin:_,relevance:0},UNDERSCORE_IDENT_RE:E,
UNDERSCORE_TITLE_MODE:{scope:"title",begin:E,relevance:0}});function A(e,t){
"."===e.input[e.index-1]&&t.ignoreMatch()}function T(e,t){
void 0!==e.className&&(e.scope=e.className,delete e.className)}function j(e,t){
t&&e.beginKeywords&&(e.begin="\\b("+e.beginKeywords.split(" ").join("|")+")(?!\\.)(?=\\b|\\s)",
e.__beforeBegin=A,e.keywords=e.keywords||e.beginKeywords,delete e.beginKeywords,
void 0===e.relevance&&(e.relevance=0))}function L(e,t){
Array.isArray(e.illegal)&&(e.illegal=p(...e.illegal))}function B(e,t){
if(e.match){
if(e.begin||e.end)throw Error("begin & end are not supported with match")
;e.begin=e.match,delete e.match}}function D(e,t){
void 0===e.relevance&&(e.relevance=1)}const C=(e,t)=>{if(!e.beforeMatch)return
;if(e.starts)throw Error("beforeMatch cannot be used with starts")
;const n=Object.assign({},e);Object.keys(e).forEach((t=>{delete e[t]
})),e.keywords=n.keywords,e.begin=h(n.beforeMatch,g(n.begin)),e.starts={
relevance:0,contains:[Object.assign(n,{endsParent:!0})]
},e.relevance=0,delete n.beforeMatch
},P=["of","and","for","in","not","or","if","then","parent","list","value"]
;function H(e,t,n="keyword"){const i=Object.create(null)
;return"string"==typeof e?s(n,e.split(" ")):Array.isArray(e)?s(n,e):Object.keys(e).forEach((n=>{
Object.assign(i,H(e[n],t,n))})),i;function s(e,n){
t&&(n=n.map((e=>e.toLowerCase()))),n.forEach((t=>{const n=t.split("|")
;i[n[0]]=[e,$(n[0],n[1])]}))}}function $(e,t){
return t?Number(t):(e=>P.includes(e.toLowerCase()))(e)?0:1}const z={},U=e=>{
console.error(e)},F=(e,...t)=>{console.log("WARN: "+e,...t)},W=(e,t)=>{
z[`${e}/${t}`]||(console.log(`Deprecated as of ${e}. ${t}`),z[`${e}/${t}`]=!0)
},G=Error();function X(e,t,{key:n}){let i=0;const s=e[n],r={},o={}
;for(let e=1;e<=t.length;e++)o[e+i]=s[e],r[e+i]=!0,i+=f(t[e-1])
;e[n]=o,e[n]._emit=r,e[n]._multi=!0}function K(e){(e=>{
e.scope&&"object"==typeof e.scope&&null!==e.scope&&(e.beginScope=e.scope,
delete e.scope)})(e),"string"==typeof e.beginScope&&(e.beginScope={
_wrap:e.beginScope}),"string"==typeof e.endScope&&(e.endScope={_wrap:e.endScope
}),(e=>{if(Array.isArray(e.begin)){
if(e.skip||e.excludeBegin||e.returnBegin)throw U("skip, excludeBegin, returnBegin not compatible with beginScope: {}"),
G
;if("object"!=typeof e.beginScope||null===e.beginScope)throw U("beginScope must be object"),
G;X(e,e.begin,{key:"beginScope"}),e.begin=m(e.begin,{joinWith:""})}})(e),(e=>{
if(Array.isArray(e.end)){
if(e.skip||e.excludeEnd||e.returnEnd)throw U("skip, excludeEnd, returnEnd not compatible with endScope: {}"),
G
;if("object"!=typeof e.endScope||null===e.endScope)throw U("endScope must be object"),
G;X(e,e.end,{key:"endScope"}),e.end=m(e.end,{joinWith:""})}})(e)}function Z(e){
function t(t,n){
return RegExp(l(t),"m"+(e.case_insensitive?"i":"")+(e.unicodeRegex?"u":"")+(n?"g":""))
}class n{constructor(){
this.matchIndexes={},this.regexes=[],this.matchAt=1,this.position=0}
addRule(e,t){
t.position=this.position++,this.matchIndexes[this.matchAt]=t,this.regexes.push([t,e]),
this.matchAt+=f(e)+1}compile(){0===this.regexes.length&&(this.exec=()=>null)
;const e=this.regexes.map((e=>e[1]));this.matcherRe=t(m(e,{joinWith:"|"
}),!0),this.lastIndex=0}exec(e){this.matcherRe.lastIndex=this.lastIndex
;const t=this.matcherRe.exec(e);if(!t)return null
;const n=t.findIndex(((e,t)=>t>0&&void 0!==e)),i=this.matchIndexes[n]
;return t.splice(0,n),Object.assign(t,i)}}class s{constructor(){
this.rules=[],this.multiRegexes=[],
this.count=0,this.lastIndex=0,this.regexIndex=0}getMatcher(e){
if(this.multiRegexes[e])return this.multiRegexes[e];const t=new n
;return this.rules.slice(e).forEach((([e,n])=>t.addRule(e,n))),
t.compile(),this.multiRegexes[e]=t,t}resumingScanAtSamePosition(){
return 0!==this.regexIndex}considerAll(){this.regexIndex=0}addRule(e,t){
this.rules.push([e,t]),"begin"===t.type&&this.count++}exec(e){
const t=this.getMatcher(this.regexIndex);t.lastIndex=this.lastIndex
;let n=t.exec(e)
;if(this.resumingScanAtSamePosition())if(n&&n.index===this.lastIndex);else{
const t=this.getMatcher(0);t.lastIndex=this.lastIndex+1,n=t.exec(e)}
return n&&(this.regexIndex+=n.position+1,
this.regexIndex===this.count&&this.considerAll()),n}}
if(e.compilerExtensions||(e.compilerExtensions=[]),
e.contains&&e.contains.includes("self"))throw Error("ERR: contains `self` is not supported at the top-level of a language.  See documentation.")
;return e.classNameAliases=i(e.classNameAliases||{}),function n(r,o){const a=r
;if(r.isCompiled)return a
;[T,B,K,C].forEach((e=>e(r,o))),e.compilerExtensions.forEach((e=>e(r,o))),
r.__beforeBegin=null,[j,L,D].forEach((e=>e(r,o))),r.isCompiled=!0;let c=null
;return"object"==typeof r.keywords&&r.keywords.$pattern&&(r.keywords=Object.assign({},r.keywords),
c=r.keywords.$pattern,
delete r.keywords.$pattern),c=c||/\w+/,r.keywords&&(r.keywords=H(r.keywords,e.case_insensitive)),
a.keywordPatternRe=t(c,!0),
o&&(r.begin||(r.begin=/\B|\b/),a.beginRe=t(a.begin),r.end||r.endsWithParent||(r.end=/\B|\b/),
r.end&&(a.endRe=t(a.end)),
a.terminatorEnd=l(a.end)||"",r.endsWithParent&&o.terminatorEnd&&(a.terminatorEnd+=(r.end?"|":"")+o.terminatorEnd)),
r.illegal&&(a.illegalRe=t(r.illegal)),
r.contains||(r.contains=[]),r.contains=[].concat(...r.contains.map((e=>(e=>(e.variants&&!e.cachedVariants&&(e.cachedVariants=e.variants.map((t=>i(e,{
variants:null},t)))),e.cachedVariants?e.cachedVariants:q(e)?i(e,{
starts:e.starts?i(e.starts):null
}):Object.isFrozen(e)?i(e):e))("self"===e?r:e)))),r.contains.forEach((e=>{n(e,a)
})),r.starts&&n(r.starts,o),a.matcher=(e=>{const t=new s
;return e.contains.forEach((e=>t.addRule(e.begin,{rule:e,type:"begin"
}))),e.terminatorEnd&&t.addRule(e.terminatorEnd,{type:"end"
}),e.illegal&&t.addRule(e.illegal,{type:"illegal"}),t})(a),a}(e)}function q(e){
return!!e&&(e.endsWithParent||q(e.starts))}class V extends Error{
constructor(e,t){super(e),this.name="HTMLInjectionError",this.html=t}}
const J=n,Q=i,Y=Symbol("nomatch"),ee=n=>{
const i=Object.create(null),s=Object.create(null),r=[];let o=!0
;const a="Could not find the language '{}', did you forget to load/include a language module?",l={
disableAutodetect:!0,name:"Plain text",contains:[]};let f={
ignoreUnescapedHTML:!1,throwUnescapedHTML:!1,noHighlightRe:/^(no-?highlight)$/i,
languageDetectRe:/\blang(?:uage)?-([\w-]+)\b/i,classPrefix:"hljs-",
cssSelector:"pre code",languages:null,__emitter:c};function b(e){
return f.noHighlightRe.test(e)}function m(e,t,n){let i="",s=""
;"object"==typeof t?(i=e,
n=t.ignoreIllegals,s=t.language):(W("10.7.0","highlight(lang, code, ...args) has been deprecated."),
W("10.7.0","Please use highlight(code, options) instead.\nhttps://github.com/highlightjs/highlight.js/issues/2277"),
s=e,i=t),void 0===n&&(n=!0);const r={code:i,language:s};O("before:highlight",r)
;const o=r.result?r.result:_(r.language,r.code,n)
;return o.code=r.code,O("after:highlight",o),o}function _(e,n,s,r){
const c=Object.create(null);function l(){if(!O.keywords)return void M.addText(R)
;let e=0;O.keywordPatternRe.lastIndex=0;let t=O.keywordPatternRe.exec(R),n=""
;for(;t;){n+=R.substring(e,t.index)
;const s=x.case_insensitive?t[0].toLowerCase():t[0],r=(i=s,O.keywords[i]);if(r){
const[e,i]=r
;if(M.addText(n),n="",c[s]=(c[s]||0)+1,c[s]<=7&&(I+=i),e.startsWith("_"))n+=t[0];else{
const n=x.classNameAliases[e]||e;u(t[0],n)}}else n+=t[0]
;e=O.keywordPatternRe.lastIndex,t=O.keywordPatternRe.exec(R)}var i
;n+=R.substring(e),M.addText(n)}function g(){null!=O.subLanguage?(()=>{
if(""===R)return;let e=null;if("string"==typeof O.subLanguage){
if(!i[O.subLanguage])return void M.addText(R)
;e=_(O.subLanguage,R,!0,S[O.subLanguage]),S[O.subLanguage]=e._top
}else e=E(R,O.subLanguage.length?O.subLanguage:null)
;O.relevance>0&&(I+=e.relevance),M.__addSublanguage(e._emitter,e.language)
})():l(),R=""}function u(e,t){
""!==e&&(M.startScope(t),M.addText(e),M.endScope())}function d(e,t){let n=1
;const i=t.length-1;for(;n<=i;){if(!e._emit[n]){n++;continue}
const i=x.classNameAliases[e[n]]||e[n],s=t[n];i?u(s,i):(R=s,l(),R=""),n++}}
function h(e,t){
return e.scope&&"string"==typeof e.scope&&M.openNode(x.classNameAliases[e.scope]||e.scope),
e.beginScope&&(e.beginScope._wrap?(u(R,x.classNameAliases[e.beginScope._wrap]||e.beginScope._wrap),
R=""):e.beginScope._multi&&(d(e.beginScope,t),R="")),O=Object.create(e,{parent:{
value:O}}),O}function p(e,n,i){let s=((e,t)=>{const n=e&&e.exec(t)
;return n&&0===n.index})(e.endRe,i);if(s){if(e["on:end"]){const i=new t(e)
;e["on:end"](n,i),i.isMatchIgnored&&(s=!1)}if(s){
for(;e.endsParent&&e.parent;)e=e.parent;return e}}
if(e.endsWithParent)return p(e.parent,n,i)}function b(e){
return 0===O.matcher.regexIndex?(R+=e[0],1):(j=!0,0)}function m(e){
const t=e[0],i=n.substring(e.index),s=p(O,e,i);if(!s)return Y;const r=O
;O.endScope&&O.endScope._wrap?(g(),
u(t,O.endScope._wrap)):O.endScope&&O.endScope._multi?(g(),
d(O.endScope,e)):r.skip?R+=t:(r.returnEnd||r.excludeEnd||(R+=t),
g(),r.excludeEnd&&(R=t));do{
O.scope&&M.closeNode(),O.skip||O.subLanguage||(I+=O.relevance),O=O.parent
}while(O!==s.parent);return s.starts&&h(s.starts,e),r.returnEnd?0:t.length}
let y={};function w(i,r){const a=r&&r[0];if(R+=i,null==a)return g(),0
;if("begin"===y.type&&"end"===r.type&&y.index===r.index&&""===a){
if(R+=n.slice(r.index,r.index+1),!o){const t=Error(`0 width match regex (${e})`)
;throw t.languageName=e,t.badRule=y.rule,t}return 1}
if(y=r,"begin"===r.type)return(e=>{
const n=e[0],i=e.rule,s=new t(i),r=[i.__beforeBegin,i["on:begin"]]
;for(const t of r)if(t&&(t(e,s),s.isMatchIgnored))return b(n)
;return i.skip?R+=n:(i.excludeBegin&&(R+=n),
g(),i.returnBegin||i.excludeBegin||(R=n)),h(i,e),i.returnBegin?0:n.length})(r)
;if("illegal"===r.type&&!s){
const e=Error('Illegal lexeme "'+a+'" for mode "'+(O.scope||"<unnamed>")+'"')
;throw e.mode=O,e}if("end"===r.type){const e=m(r);if(e!==Y)return e}
if("illegal"===r.type&&""===a)return r.index===n.length||(R+="\n"),1
;if(T>1e5&&T>3*r.index)throw Error("potential infinite loop, way more iterations than matches")
;return R+=a,a.length}const x=k(e)
;if(!x)throw U(a.replace("{}",e)),Error('Unknown language: "'+e+'"')
;const N=Z(x);let v="",O=r||N;const S={},M=new f.__emitter(f);(()=>{const e=[]
;for(let t=O;t!==x;t=t.parent)t.scope&&e.unshift(t.scope)
;e.forEach((e=>M.openNode(e)))})();let R="",I=0,A=0,T=0,j=!1;try{
if(x.__emitTokens)x.__emitTokens(n,M);else{for(O.matcher.considerAll();;){
T++,j?j=!1:O.matcher.considerAll(),O.matcher.lastIndex=A
;const e=O.matcher.exec(n);if(!e)break;const t=w(n.substring(A,e.index),e)
;A=e.index+t}w(n.substring(A))}return M.finalize(),v=M.toHTML(),{language:e,
value:v,relevance:I,illegal:!1,_emitter:M,_top:O}}catch(t){
if(t.message&&t.message.includes("Illegal"))return{language:e,value:J(n),
illegal:!0,relevance:0,_illegalBy:{message:t.message,index:A,
context:n.slice(A-100,A+100),mode:t.mode,resultSoFar:v},_emitter:M};if(o)return{
language:e,value:J(n),illegal:!1,relevance:0,errorRaised:t,_emitter:M,_top:O}
;throw t}}function E(e,t){t=t||f.languages||Object.keys(i);const n=(e=>{
const t={value:J(e),illegal:!1,relevance:0,_top:l,_emitter:new f.__emitter(f)}
;return t._emitter.addText(e),t})(e),s=t.filter(k).filter(v).map((t=>_(t,e,!1)))
;s.unshift(n);const r=s.sort(((e,t)=>{
if(e.relevance!==t.relevance)return t.relevance-e.relevance
;if(e.language&&t.language){if(k(e.language).supersetOf===t.language)return 1
;if(k(t.language).supersetOf===e.language)return-1}return 0})),[o,a]=r,c=o
;return c.secondBest=a,c}function y(e){let t=null;const n=(e=>{
let t=e.className+" ";t+=e.parentNode?e.parentNode.className:""
;const n=f.languageDetectRe.exec(t);if(n){const t=k(n[1])
;return t||(F(a.replace("{}",n[1])),
F("Falling back to no-highlight mode for this block.",e)),t?n[1]:"no-highlight"}
return t.split(/\s+/).find((e=>b(e)||k(e)))})(e);if(b(n))return
;if(O("before:highlightElement",{el:e,language:n
}),e.dataset.highlighted)return void console.log("Element previously highlighted. To highlight again, first unset `dataset.highlighted`.",e)
;if(e.children.length>0&&(f.ignoreUnescapedHTML||(console.warn("One of your code blocks includes unescaped HTML. This is a potentially serious security risk."),
console.warn("https://github.com/highlightjs/highlight.js/wiki/security"),
console.warn("The element with unescaped HTML:"),
console.warn(e)),f.throwUnescapedHTML))throw new V("One of your code blocks includes unescaped HTML.",e.innerHTML)
;t=e;const i=t.textContent,r=n?m(i,{language:n,ignoreIllegals:!0}):E(i)
;e.innerHTML=r.value,e.dataset.highlighted="yes",((e,t,n)=>{const i=t&&s[t]||n
;e.classList.add("hljs"),e.classList.add("language-"+i)
})(e,n,r.language),e.result={language:r.language,re:r.relevance,
relevance:r.relevance},r.secondBest&&(e.secondBest={
language:r.secondBest.language,relevance:r.secondBest.relevance
}),O("after:highlightElement",{el:e,result:r,text:i})}let w=!1;function x(){
if("loading"===document.readyState)return w||window.addEventListener("DOMContentLoaded",(()=>{
x()}),!1),void(w=!0);document.querySelectorAll(f.cssSelector).forEach(y)}
function k(e){return e=(e||"").toLowerCase(),i[e]||i[s[e]]}
function N(e,{languageName:t}){"string"==typeof e&&(e=[e]),e.forEach((e=>{
s[e.toLowerCase()]=t}))}function v(e){const t=k(e)
;return t&&!t.disableAutodetect}function O(e,t){const n=e;r.forEach((e=>{
e[n]&&e[n](t)}))}Object.assign(n,{highlight:m,highlightAuto:E,highlightAll:x,
highlightElement:y,
highlightBlock:e=>(W("10.7.0","highlightBlock will be removed entirely in v12.0"),
W("10.7.0","Please use highlightElement now."),y(e)),configure:e=>{f=Q(f,e)},
initHighlighting:()=>{
x(),W("10.6.0","initHighlighting() deprecated.  Use highlightAll() now.")},
initHighlightingOnLoad:()=>{
x(),W("10.6.0","initHighlightingOnLoad() deprecated.  Use highlightAll() now.")
},registerLanguage:(e,t)=>{let s=null;try{s=t(n)}catch(t){
if(U("Language definition for '{}' could not be registered.".replace("{}",e)),
!o)throw t;U(t),s=l}
s.name||(s.name=e),i[e]=s,s.rawDefinition=t.bind(null,n),s.aliases&&N(s.aliases,{
languageName:e})},unregisterLanguage:e=>{delete i[e]
;for(const t of Object.keys(s))s[t]===e&&delete s[t]},
listLanguages:()=>Object.keys(i),getLanguage:k,registerAliases:N,
autoDetection:v,inherit:Q,addPlugin:e=>{(e=>{
e["before:highlightBlock"]&&!e["before:highlightElement"]&&(e["before:highlightElement"]=t=>{
e["before:highlightBlock"](Object.assign({block:t.el},t))
}),e["after:highlightBlock"]&&!e["after:highlightElement"]&&(e["after:highlightElement"]=t=>{
e["after:highlightBlock"](Object.assign({block:t.el},t))})})(e),r.push(e)},
removePlugin:e=>{const t=r.indexOf(e);-1!==t&&r.splice(t,1)}}),n.debugMode=()=>{
o=!1},n.safeMode=()=>{o=!0},n.versionString="11.11.1",n.regex={concat:h,
lookahead:g,either:p,optional:d,anyNumberOfTimes:u}
;for(const t in I)"object"==typeof I[t]&&e(I[t]);return Object.assign(n,I),n
},te=ee({});te.newInstance=()=>ee({})
;const ne="([ui](8|16|32|64|128|size)|f(32|64)|int)?",ie=["abstract","as","async","await","become","box","break","const","continue","crate","do","dyn","else","enum","extern","final","fn","for","if","impl","in","let","loop","macro","match","mod","move","mut","override","priv","pub","ref","return","self","Self","static","struct","super","trait","try","type","typeof","union","unsafe","unsized","use","virtual","where","while","yield"],se=["true","false","Some","None","Ok","Err"],re=["i8","i16","i32","i64","i128","isize","u8","u16","u32","u64","u128","usize","f32","f64","str","char","bool","Box","Option","Result","String","Vec"],oe=["DeepModel","FMap","FSet","Ghost","Id","Int","Invariant","Mapping","PermCell","PermCellOwn","PeanoInt","PredCell","PtrOwn","Real","Resolve","Seq","Set","Snapshot","View"],ae=["forall","exists"].concat(ie)
;function ce(e){const t={className:"title.function.invoke",relevance:0,
begin:e.regex.concat(/\b/,/(?!(?:let|for|while|if|else|match)\b)/,e.IDENT_RE,e.regex.lookahead(/\s*\(/))
};return{pearlite:[e.C_LINE_COMMENT_MODE,e.COMMENT("/\\*","\\*/",{
contains:["self"]}),{scope:"number",variants:[{begin:"\\b0b([01_]+)"+ne},{
begin:"\\b0o([0-7_]+)"+ne},{begin:"\\b0x([A-Fa-f0-9_]+)"+ne},{
begin:"\\b(\\d[\\d_]*(\\.[0-9_]+)?([eE][+-]?[0-9_]+)?)"+ne}]},t]}}
var le=Object.freeze({__proto__:null,grmr_pearlite:e=>{const t=ce(e).pearlite
;return{name:"Pearlite",aliases:[],literals:se,keywords:{keyword:ae,type:re,
"creusot-type":oe},contains:t}},grmr_rust:e=>{
const t=ce(e).pearlite,n=e.regex,i=/(r#)?/,s=n.concat(i,e.UNDERSCORE_IDENT_RE),r=n.concat(i,e.IDENT_RE),o={
className:"title.function.invoke",relevance:0,
begin:n.concat(/\b/,/(?!(?:let|for|while|if|else|match)\b)/,r,n.lookahead(/\s*\(/))
},a=["drop ","Copy","Send","Sized","Sync","Drop","Fn","FnMut","FnOnce","ToOwned","Clone","Debug","PartialEq","PartialOrd","Eq","Ord","AsRef","AsMut","Into","From","Default","Iterator","Extend","IntoIterator","DoubleEndedIterator","ExactSizeIterator","SliceConcatExt","ToString","assert!","assert_eq!","bitflags!","bytes!","cfg!","col!","concat!","concat_idents!","debug_assert!","debug_assert_eq!","env!","eprintln!","panic!","file!","format!","format_args!","include_bytes!","include_str!","line!","local_data_key!","module_path!","option_env!","print!","println!","select!","stringify!","try!","unimplemented!","unreachable!","vec!","write!","writeln!","macro_rules!","assert_ne!","debug_assert_ne!"]
;return{name:"Rust",aliases:["rs"],keywords:{$pattern:e.IDENT_RE+"!?",type:re,
"creusot-type":oe,keyword:ie,literal:se,built_in:a},illegal:"</",
contains:[e.C_LINE_COMMENT_MODE,e.COMMENT("/\\*","\\*/",{contains:["self"]
}),e.inherit(e.QUOTE_STRING_MODE,{begin:/b?"/,illegal:null}),{
className:"symbol",begin:/'[a-zA-Z_][a-zA-Z0-9_]*(?!')/},{scope:"string",
variants:[{begin:/b?r(#*)"(.|\n)*?"\1(?!#)/},{begin:/b?'/,end:/'/,contains:[{
scope:"char.escape",match:/\\('|\w|x\w{2}|u\w{4}|U\w{8})/}]}]},{
className:"number",variants:[{begin:"\\b0b([01_]+)"+ne},{
begin:"\\b0o([0-7_]+)"+ne},{begin:"\\b0x([A-Fa-f0-9_]+)"+ne},{
begin:"\\b(\\d[\\d_]*(\\.[0-9_]+)?([eE][+-]?[0-9_]+)?)"+ne}],relevance:0},{
begin:[/fn/,/\s+/,s],className:{1:"keyword",3:"title.function"}},{
scope:"keyword.creusot",match:/\bghost\s*!/},{className:"meta",begin:"#!?\\[",
end:"\\]",keywords:{
"keyword.creusot":["law","logic","check","open","prophetic","terminates","trusted","ghost","erasure","private"]
},contains:[{scope:"creusot",begin:/(?:requires|ensures|invariant|variant)\(/,
beginScope:"keyword.creusot",endScope:"keyword.creusot",end:/[()]/,
"on:begin":(e,t)=>{t.data.nesting=0},"on:end":(e,t)=>{
"("===e[0]?(t.data.nesting++,
t.ignoreMatch()):0!==t.data.nesting&&(t.data.nesting--,t.ignoreMatch())},
literals:se,contains:t,keywords:ae},{className:"string",begin:/"/,end:/"/,
contains:[e.BACKSLASH_ESCAPE]}]},{scope:"creusot",beginScope:"keyword.creusot",
endScope:"keyword.creusot",contains:t,keywords:ae,"on:begin":(e,t)=>{
t.data.nesting=0},"on:end":(e,t)=>{
"("===e[0]||"["===e[0]||"{"===e[0]?(t.data.nesting++,
t.ignoreMatch()):0!==t.data.nesting&&(t.data.nesting--,t.ignoreMatch())},
variants:[{begin:/\b(?:snapshot|proof_assert|pearlite)\s*!\s*\(/,end:/[()]/},{
begin:/\b(?:snapshot|proof_assert|pearlite)\s*!\s*\[/,end:/[\[\]]/},{
begin:/\b(?:snapshot|proof_assert|pearlite)\s*!\s*{/,end:/[{}]/}]},{
begin:[/let/,/\s+/,/(?:mut\s+)?/,s],className:{1:"keyword",3:"keyword",
4:"variable"}},{begin:[/for/,/\s+/,s,/\s+/,/in/],className:{1:"keyword",
3:"variable",5:"keyword"}},{begin:[/type/,/\s+/,s],className:{1:"keyword",
3:"title.class"}},{begin:[/(?:trait|enum|struct|union|impl|for)/,/\s+/,s],
className:{1:"keyword",3:"title.class"}},{begin:e.IDENT_RE+"::",keywords:{
keyword:"Self",built_in:a,type:re,"creusot-type":oe}},{className:"punctuation",
begin:"->"},o]}}});const ge=te;for(const e of Object.keys(le)){
const t=e.replace("grmr_","").replace("_","-");ge.registerLanguage(t,le[e])}
return ge}()
;"object"==typeof exports&&"undefined"!=typeof module&&(module.exports=hljs);