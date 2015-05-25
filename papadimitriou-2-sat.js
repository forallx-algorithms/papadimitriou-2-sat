/*
  Papadimitriou 2-sat alghorithm

  @author Evgeniy Kuznetsov
  @date 11.05.2015
*/

// Papadimitriou 2-sat
// @param {Array.<Array>} ins Instance of a problem
// @return {Boolean} true - satisfiable, false otherwise
function solve2Sat(ins) {
  ins = cleanInstance(ins);

  var rulesDict = createRulesDictionary(ins);
  var bits = Object.keys(rulesDict);

  var endpoint1 = Math.round(Math.log(bits.length) / Math.LN2);
  var endpoint2 = 2 * Math.pow(bits.length, 2);
  for(var i = 0; i <= endpoint1; i++) {
    var assignment = makeRandomAssignment(ins);

    var previousChanged = undefined,
        previousUnsat = undefined;

    for(var j = 0; j <= endpoint2; j++) {
      var unsat = checkSat(assignment, ins, previousUnsat, previousChanged, rulesDict);

      if(unsat.length == 0) {
        return true;

      } else {
        var randrule = Math.floor(Math.random() * unsat.length);
        randrule = unsat[randrule];

        var randbit = Math.floor(Math.random() * 2);
        randbit = Math.abs(randrule[randbit]);

        assignment[randbit] = !assignment[randbit];

        previousChanged = randbit;
        previousUnsat = unsat;
      }
    }
  }

  return ins.length == 0 ? true : false;
}

// section: Helpers

// Calculate all bits of a given instance
// @param {Array} ins
// @return {Object}
function calculateBits(ins) {
  var r = {};

  for(var i in ins) {
    r[Math.abs(ins[i][0])] = null;
    r[Math.abs(ins[i][1])] = null;
  }

  return r;
}

// Makes random assignment to a given instance
// @param {Array} ins
// @return {Object}
function makeRandomAssignment(ins) {
  var bits = calculateBits(ins);
  var keys = Object.keys(bits);

  for(var i in keys) {
    bits[keys[i]] = Boolean(Math.floor(Math.random() * 2));
  }

  return bits;
}

// Creates rules dictionary
// @param {Array} ins
// @return {Object}
function createRulesDictionary(ins) {
  var r = {};

  var pushToDict = function(id, rule) {
    if(!r[id]) r[id] = [];
    r[id].push(rule);
  };

  for(var i in ins) {
    var rule = ins[i];

    pushToDict(Math.abs(rule[0]), rule);
    pushToDict(Math.abs(rule[1]), rule);
  }

  return r;
}

// Check if assignment satisfied
// @param {Object} assignment
// @param {Array} ins
// @param {Array} previousUnsat Previously unsatisfied rules
// @param {Integer} changedBit Currently changed bit
// @param {Object} rulesDict
// @return {Array.<Array>}
function checkSat(assignment, ins, previousUnsat, changedBit, rulesDict) {

  // Check all rules
  // @return {Boolean} true - satisfied, otherwise false
  function checkRule(rule) {
    var first = rule[0];
    var second = rule[1];

    var firstShould = first >= 0;
    var secondShould = second >= 0;

    var firstIs = assignment[Math.abs(first)];
    var secondIs = assignment[Math.abs(second)];

    return firstShould == firstIs || secondShould == secondIs;
  }

  function checkFull() {
    var r = [];
    for(var i in ins) {
      var rule = ins[i];
      if(!checkRule(rule)) {
        r.push(rule);
      }
    }

    return r;
  }

  // Check rules only affected by current change
  function checkChanged() {
    previousUnsat = previousUnsat.slice(0);

    var currentUnsat = [];
    var unsatRulesIds = previousUnsat.map(function(r){ return cantorPairing(r[0], r[1]); });

    var dictEntry = rulesDict[changedBit];

    var excludedIndices = [];

    for(var i = 0; i < dictEntry.length; i++) {
      var rule = dictEntry[i];
      var ruleId = cantorPairing(rule[0], rule[1]);

      var ruleI = unsatRulesIds.indexOf(ruleId);

      if(checkRule(rule)) {

        if(ruleI != -1) {
          excludedIndices.push(ruleI);
        }

      } else if(ruleI == -1) {
        currentUnsat.push(rule);
      }
    }

    var del = 0;
    for(var z in excludedIndices){
      previousUnsat.splice(excludedIndices[z] - del, 1);
      del++;
    }
    return previousUnsat.concat(currentUnsat);

  }

  var result;
  if(typeof(previousUnsat) != "undefined" && typeof(changedBit) != "undefined") {
    result = checkChanged();
  } else {
    result = checkFull();
  }

  return result;

}

// Clear instance from unnecessary rules
// @param {Array} ins
// @return {Array}
function cleanInstance(ins) {
  ins = ins.slice(0);

  var lookup, constants;

  var checkInstance = function(v) {
    var cv = v * -1;
    var skey = Math.abs(v);

    var notAConstant = lookup[cv] != undefined;

    if(notAConstant) {
      delete constants[skey];
    } else {
      constants[skey] = true;
    }
  };

  while(true) {

    lookup = {};
    constants = {};

    for(var i in ins) {
      var rule = ins[i];
      var f = rule[0], s = rule[1];

      lookup[f] = true;
      lookup[s] = true;

      checkInstance(f);
      checkInstance(s);
    }

    if(Object.keys(constants).length == 0) break;

    ins = ins.filter(function(r, i){
      return constants[Math.abs(r[0])] == undefined && constants[Math.abs(r[1])] == undefined;
    });
  }

  return ins;
}

// Cantor pairing function
// http://en.wikipedia.org/wiki/Pairing_function
// @param {Integer} a
// @param {Integer} b
// @return {Integer}
function cantorPairing(a, b) {
  var ca = a >= 0 ? 2 * a : -2 * a - 1;
  var cb = b >= 0 ? 2 * b : -2 * b - 1;
  return ((ca + cb) * (ca + cb + 1))/2 + ca;
}


// section: Tests
var cleanableSat = [
  [1, 2],
  [-2, 1],
  [2, 3],
  [2, -3]
];

var simple = [
  [1, 2],
  [-1, 3],
  [3, 4],
  [-2, -4]
];

var simpleUnsat = [
  [2, 2],
  [-2, -2]
];

var uncorrectSimpleAssignment = {
  '1': false,
  '2': false,
  '3': false,
  '4': false
};

var correctSimpleAssignment = {
  '1': true,
  '2': false,
  '3': true,
  '4': false
};

console.log("Case 1:", solve2Sat(simple)==true);

console.log("Case 2:", Object.keys(calculateBits(simple)).length == 4, calculateBits(simple));
console.log("Case 3:", makeRandomAssignment(simple));

console.log("Case 4:", checkSat(uncorrectSimpleAssignment, simple).length > 0, checkSat(uncorrectSimpleAssignment, simple));
console.log("Case 5:", checkSat(correctSimpleAssignment, simple).length == 0, checkSat(correctSimpleAssignment, simple));

console.log("Case 6:", solve2Sat(simpleUnsat)==false);

console.log("Case 7a:", cleanInstance(cleanableSat));
console.log("Case 7b:", cleanInstance(simpleUnsat));

console.log("Case 8:", createRulesDictionary(simple));




