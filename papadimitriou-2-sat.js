/*

  @author Evgeniy Kuznetsov
  @date 11.05.2015
*/

// @param {Array.<Array>} ins Instance of a problem
// @return {Boolean} true - satisfiable, false otherwise
function solve2Sat(ins) {
  ins = cleanIns(ins);

  var startOn = Date.now();

  var rulesDict = createRulesDictionary(ins);

  var bits = calculateBits(ins);
  bits = Object.keys(bits);

  var endpoint1 = Math.round(Math.log(bits.length) / Math.LN2);
  for(var i = 0; i <= endpoint1; i++) {
    var assignment = makeRandomAssignment(ins);

    var previousChanged, previousUnsat;

    console.log("Solve sat", "Try", i, "of", endpoint1);

    var endpoint2 = bits.length;
    for(var j = 0; j <= endpoint2; j++) {

      var loopStart = Date.now();

      var progress = ((j/endpoint2)*100);

      if(Math.random()*10 > 9) console.log("Done", progress, "in", Date.now() - startOn);

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

//      console.log("Loop ended by", Date.now() - loopStart);

    }
  }

  return false;
}

// section: Helpers

// @return {Object}
function calculateBits(ins) {
  var r = {};

  for(var i in ins) {
    r[Math.abs(ins[i][0])] = null;
    r[Math.abs(ins[i][1])] = null;
  }

  return r;
}

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
// @param {Object} ins
// @return {Object}
function createRulesDictionary(ins) {
  var r = {};

  var pushToDict = function(id, rule) {
    if(!r[id]) r[id] = [];
    r[id].push(rule);
  }

  for(var i in ins) {
    var rule = ins[i];

    pushToDict(Math.abs(rule[0]), rule);
    pushToDict(Math.abs(rule[1]), rule);
  }

  return r;
}

// @return {Array.<Array>}
function checkSat(assignment, ins, previousUnsat, changedBit, rulesDict) {

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

//    console.log("Check sat", "Full", ins.length);

    for(var i in ins) {
      var rule = ins[i];
      if(!checkRule(rule)) {
        r.push(rule);
      }
    }

    return r;
  }

  function checkChanged() {
    previousUnsat = previousUnsat.slice(0);

    var currentUnsat = [];
    var unsatRulesIds = previousUnsat.map(function(r){ return r[0]+r[1] });

    var dictEntry = rulesDict[changedBit];

    var excludedIndices = [];

    for(var i = 0; i < dictEntry.length; i++) {
      var rule = dictEntry[i];
      var ruleId = rule[0]+rule[1];

      var ruleI = unsatRulesIds.indexOf(ruleId);

      if(checkRule(rule)) {

        if(ruleI != -1) {
          excludedIndices.push(ruleI);
        }

      } else if(ruleI == -1) {
        currentUnsat.push(rule);
      }
    }

    var debugS = Date.now();
    var del = 0;
    for(var z in excludedIndices){
      previousUnsat.splice(excludedIndices[z] - del, 1);
      del++;
    }
//    console.log("Ended by", Date.now() - debugS);

    return previousUnsat.concat(currentUnsat);

  }

  var debugProcStart = Date.now();

  var result;

  if(typeof(previousUnsat) != "undefined" && typeof(changedBit) != "undefined") {
    result = checkChanged();
  } else {
    result = checkFull();
  }

//  console.log("Check sat end in", Date.now() - debugProcStart);
  return result;

}

// Cleans instance from unnecessary rules
function cleanIns(ins) {
  var inscopy = ins.slice(0, Infinity);
  var bits = calculateBits(ins);
  var bitsa = Object.keys(bits);
  bitsa = bitsa.map(function(b){ return parseInt(b); });
  var constant = {};

  var debugS = Date.now();

  for(var i in bitsa) {

    if(i%100 == 0) console.log("Preprocessing", i, "of", bitsa.length, Date.now() - debugS);

    var bit = bitsa[i];
    var rulesi = [];

    var isconst = true;

    var value;

    var debugS2 = Date.now();
    for(var j in inscopy) {
      var first = inscopy[j][0];
      var second = inscopy[j][1];

      var isf = Math.abs(first) == bit;
      var iss = Math.abs(second) == bit;

      if(isf || iss) {
        rulesi.push(parseInt(j));
        var cvalue;

        if(isf) cvalue = first >= 0;
        if(iss) cvalue = second >= 0;

        if(value == undefined) value = cvalue;

        if(value != cvalue) {
          isconst = false;
          break;
        }
      }
    }
    console.log("Ended by", Date.now() - debugS2);

    if(isconst && rulesi.length > 0) {
      constant[bit] = value;

      var throwaway = function(i) {
        inscopy.splice(i, 1);
        return inscopy;
      }

      inscopy = throwaway(rulesi[0]);

      for(var i = 1; i < rulesi.length; i++) {
        inscopy = throwaway(rulesi[i] - 1);
      }
    }
  }

  return inscopy;
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
}

console.log("Case 1:", solve2Sat(simple)==true);

console.log("Case 2:", Object.keys(calculateBits(simple)).length == 4, calculateBits(simple));
console.log("Case 3:", makeRandomAssignment(simple));

console.log("Case 4:", checkSat(uncorrectSimpleAssignment, simple).length > 0, checkSat(uncorrectSimpleAssignment, simple));
console.log("Case 5:", checkSat(correctSimpleAssignment, simple).length == 0, checkSat(correctSimpleAssignment, simple));

console.log("Case 6:", solve2Sat(simpleUnsat)==false);

console.log("Case 7:", cleanIns(cleanableSat));

console.log("Case 8:", createRulesDictionary(simple));

// section: solutions






