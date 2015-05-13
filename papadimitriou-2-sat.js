/*

  @author Evgeniy Kuznetsov
  @date 11.05.2015
*/

// @param {Array.<Array>} ins Instance of a problem
// @return {Boolean} true - satisfiable, false otherwise
function solve2Sat(ins) {
  ins = cleanIns(ins);

  var bits = calculateBits(ins);
  bits = Object.keys(bits);

  console.log("Bits is", bits.length);

  var endpoint1 = Math.round(Math.log(bits.length) / Math.LN2);
  for(var i = 0; i <= endpoint1; i++) {
    var assignment = makeRandomAssignment(ins);

    console.log("Trial", i, "of", endpoint1);

    var endpoint2 = bits.length;
    for(var j = 0; j <= endpoint2; j++) {
      var unsat = checkSat(assignment, ins);

      if(unsat.length == 0) {
        console.log("Found", assignment);
        return true;

      } else {
        var randrule = Math.floor(Math.random() * unsat.length);
        randrule = unsat[randrule];

        var randbit = Math.floor(Math.random() * 2);
        randbit = Math.abs(unsat[randbit]);

        assignment[randbit] = !assignment[randbit];
      }

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
function checkSat(assignment, ins) {
  var r = [];

  for(var i in ins) {
    var rule = ins[i];

    var first = rule[0];
    var second = rule[1];

    var firstShould = first >= 0;
    var secondShould = second >= 0;

    var firstIs = assignment[Math.abs(first)];
    var secondIs = assignment[Math.abs(second)];

    if(firstShould != firstIs && secondShould != secondIs) {
      r.push(rule);
    }
  }

  return r;
}

// Cleans instance from unnecessary rules
function cleanIns(ins) {
  var inscopy = ins.slice(0, Infinity);
  var bits = calculateBits(ins);
  var bitsa = Object.keys(bits);
  bitsa = bitsa.map(function(b){ return parseInt(b); });
  var constant = {};

  for(var i in bitsa) {
    console.log("Preprocessing", i, "of", bitsa.length);
    var bit = bitsa[i];
    var rulesi = [];

    var isconst = true;

    var value;

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

    if(isconst && rulesi.length > 0) {
      constant[bit] = value;

      var throwaway = function(i) {
        var r = inscopy.slice(0, i).concat(inscopy.slice(i + 1, Infinity));
        return r;
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

