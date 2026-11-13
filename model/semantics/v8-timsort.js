/*
 * Copyright (c) 2001-2018 Python Software Foundation; All Rights Reserved.
 * Derived from V8 8.7.220.31 third_party/v8/builtins/array-sort.tq.
 * The source revision's SHA-256 is 5298236842b7cbaff0c985edd0d371d9de23c81879f1a12855d97afb54c94234.
 * Licenses: lean/licenses/V8-LICENSE and lean/licenses/PYTHON-LICENSE.
 * Explicit JavaScript translation of the pinned TimSort comparison schedule.
 * This private function receives scratch storage and captured intrinsics.
 * It does not install or replace a function in the user game.
 */
(function (workArray, comparefn, StringIntrinsic, CreateIntrinsic, length) {
  'use strict';
  var sortState = CreateIntrinsic(null);
  sortState.workArray = workArray;
  sortState.pendingRuns = CreateIntrinsic(null);
  sortState.pendingRunsSize = 0;
  sortState.minGallop = 7;
  sortState.Compare = function (x,y) {
    if (comparefn === undefined) {
      var a = StringIntrinsic(x), b = StringIntrinsic(y);
      return a < b ? -1 : b < a ? 1 : 0;
    }
    var v = +comparefn(x,y);
    return v === v ? v : 0;
  };
  var kSuccess = 0, kMinGallopWins = 7;
  function Identity(x) { return x; }
  function SmiMin(a,b) { return a < b ? a : b; }
  function SmiMax(a,b) { return a > b ? a : b; }
  function GetPendingRunsSize(s) { return s.pendingRunsSize; }
  function GetPendingRunBase(p,i) { return p[2*i]; }
  function GetPendingRunLength(p,i) { return p[2*i+1]; }
  function SetPendingRunBase(p,i,v) { p[2*i] = v; }
  function SetPendingRunLength(p,i,v) { p[2*i+1] = v; }
  function PushRun(s,base,length) {
    var i = s.pendingRunsSize++;
    s.pendingRuns[2*i] = base; s.pendingRuns[2*i+1] = length;
  }
  function GetTempArray(s,length) { return CreateIntrinsic(null); }
function Copy(
    source, srcPos, target, dstPos,
    length) {

  if (srcPos < dstPos) {
    var srcIdx = srcPos + length - 1;
    var dstIdx = dstPos + length - 1;
    while (srcIdx >= srcPos) {
      target[dstIdx--] = source[srcIdx--];
    }
  } else {
    var srcIdx = srcPos;
    var dstIdx = dstPos;
    var to = srcPos + length;

    while (srcIdx < to) {
      target[dstIdx++] = source[srcIdx++];
    }
  }
  return kSuccess;
}

function BinaryInsertionSort(
    low, startArg, high) {

  var workArray = sortState.workArray;

  var start = low == startArg ? (startArg + 1) : startArg;

  for (; start < high; ++start) {
    
    var left = low;
    var right = start;

    var pivot = Identity(workArray[right]);

    while (left < right) {
      var mid = left + ((right - left) >> 1);
      var order =
          sortState.Compare(pivot, Identity(workArray[mid]));

      if (order < 0) {
        right = mid;
      } else {
        left = mid + 1;
      }
    }

    for (var p = start; p > left; --p) {
      workArray[p] = workArray[p - 1];
    }
    workArray[left] = pivot;
  }
}

function CountAndMakeRun(
    lowArg, high) {

  var workArray = sortState.workArray;

  var low = lowArg + 1;
  if (low == high) return 1;

  var runLength = 2;

  var elementLow = Identity(workArray[low]);
  var elementLowPred = Identity(workArray[low - 1]);
  var order = sortState.Compare(elementLow, elementLowPred);

  var isDescending = order < 0 ? true : false;

  var previousElement = elementLow;
  for (var idx = low + 1; idx < high; ++idx) {
    var currentElement = Identity(workArray[idx]);
    order = sortState.Compare(currentElement, previousElement);

    if (isDescending) {
      if (order >= 0) break;
    } else {
      if (order < 0) break;
    }

    previousElement = currentElement;
    ++runLength;
  }

  if (isDescending) {
    ReverseRange(workArray, lowArg, lowArg + runLength);
  }

  return runLength;
}

function ReverseRange(array, from, to) {
  var low = from;
  var high = to - 1;

  while (low < high) {
    var elementLow = array[low];
    var elementHigh = array[high];
    array[low++] = elementHigh;
    array[high--] = elementLow;
  }
}

function MergeAt(i) {
  var stackSize = GetPendingRunsSize(sortState);

  var workArray = sortState.workArray;

  var pendingRuns = sortState.pendingRuns;
  var baseA = GetPendingRunBase(pendingRuns, i);
  var lengthA = GetPendingRunLength(pendingRuns, i);
  var baseB = GetPendingRunBase(pendingRuns, i + 1);
  var lengthB = GetPendingRunLength(pendingRuns, i + 1);

  SetPendingRunLength(pendingRuns, i, lengthA + lengthB);
  if (i == stackSize - 3) {
    var base = GetPendingRunBase(pendingRuns, i + 2);
    var length = GetPendingRunLength(pendingRuns, i + 2);
    SetPendingRunBase(pendingRuns, i + 1, base);
    SetPendingRunLength(pendingRuns, i + 1, length);
  }
  sortState.pendingRunsSize = stackSize - 1;

  var keyRight = Identity(workArray[baseB]);
  var k = GallopRight(workArray, keyRight, baseA, lengthA, 0);

  baseA = baseA + k;
  lengthA = lengthA - k;
  if (lengthA == 0) return kSuccess;

  var keyLeft = Identity(workArray[baseA + lengthA - 1]);
  lengthB = GallopLeft(workArray, keyLeft, baseB, lengthB, lengthB - 1);
  
  if (lengthB == 0) return kSuccess;

  if (lengthA <= lengthB) {
    MergeLow(baseA, lengthA, baseB, lengthB);
  } else {
    MergeHigh(baseA, lengthA, baseB, lengthB);
  }
  return kSuccess;
}

function GallopLeft(
    array, key, base, length, hint) {

  var lastOfs = 0;
  var offset = 1;

  var baseHintElement = Identity(array[base + hint]);
  var order = sortState.Compare(baseHintElement, key);

  if (order < 0) {

    var maxOfs = length - hint;
    while (offset < maxOfs) {
      var offsetElement =
          Identity(array[base + hint + offset]);
      order = sortState.Compare(offsetElement, key);

      if (order >= 0) break;

      lastOfs = offset;
      offset = (offset << 1) + 1;

      if (offset <= 0) offset = maxOfs;
    }

    if (offset > maxOfs) offset = maxOfs;

    lastOfs = lastOfs + hint;
    offset = offset + hint;
  } else {

    var maxOfs = hint + 1;
    while (offset < maxOfs) {
      var offsetElement =
          Identity(array[base + hint - offset]);
      order = sortState.Compare(offsetElement, key);

      if (order < 0) break;

      lastOfs = offset;
      offset = (offset << 1) + 1;

      if (offset <= 0) offset = maxOfs;
    }

    if (offset > maxOfs) offset = maxOfs;

    var tmp = lastOfs;
    lastOfs = hint - offset;
    offset = hint - tmp;
  }

  lastOfs++;
  while (lastOfs < offset) {
    var m = lastOfs + ((offset - lastOfs) >> 1);

    order = sortState.Compare(Identity(array[base + m]), key);

    if (order < 0) {
      lastOfs = m + 1;  
    } else {
      offset = m;  
    }
  }

  return offset;
}

function GallopRight(
    array, key, base, length, hint) {

  var lastOfs = 0;
  var offset = 1;

  var baseHintElement = Identity(array[base + hint]);
  var order = sortState.Compare(key, baseHintElement);

  if (order < 0) {

    var maxOfs = hint + 1;
    while (offset < maxOfs) {
      var offsetElement =
          Identity(array[base + hint - offset]);
      order = sortState.Compare(key, offsetElement);

      if (order >= 0) break;

      lastOfs = offset;
      offset = (offset << 1) + 1;

      if (offset <= 0) offset = maxOfs;
    }

    if (offset > maxOfs) offset = maxOfs;

    var tmp = lastOfs;
    lastOfs = hint - offset;
    offset = hint - tmp;
  } else {

    var maxOfs = length - hint;
    while (offset < maxOfs) {
      var offsetElement =
          Identity(array[base + hint + offset]);
      order = sortState.Compare(key, offsetElement);

      if (order < 0) break;

      lastOfs = offset;
      offset = (offset << 1) + 1;

      if (offset <= 0) offset = maxOfs;
    }

    if (offset > maxOfs) offset = maxOfs;

    lastOfs = lastOfs + hint;
    offset = offset + hint;
  }

  lastOfs++;
  while (lastOfs < offset) {
    var m = lastOfs + ((offset - lastOfs) >> 1);

    order = sortState.Compare(key, Identity(array[base + m]));

    if (order < 0) {
      offset = m;  
    } else {
      lastOfs = m + 1;  
    }
  }

  return offset;
}

function MergeLow(
    baseA, lengthAArg, baseB, lengthBArg) {

  var lengthA = lengthAArg;
  var lengthB = lengthBArg;

  var workArray = sortState.workArray;
  var tempArray = GetTempArray(sortState, lengthA);
  Copy(workArray, baseA, tempArray, 0, lengthA);

  var dest = baseA;
  var cursorTemp = 0;
  var cursorB = baseB;

  workArray[dest++] = workArray[cursorB++];

  {
    if (--lengthB == 0) return Succeed();
    if (lengthA == 1) return CopyB();

    var minGallop = sortState.minGallop;

    while (true) {
      var nofWinsA = 0;  
      var nofWinsB = 0;  

      while (true) {

        var order = sortState.Compare(
            Identity(workArray[cursorB]),
            Identity(tempArray[cursorTemp]));

        if (order < 0) {
          workArray[dest++] = workArray[cursorB++];

          ++nofWinsB;
          --lengthB;
          nofWinsA = 0;

          if (lengthB == 0) return Succeed();
          if (nofWinsB >= minGallop) break;
        } else {
          workArray[dest++] = tempArray[cursorTemp++];

          ++nofWinsA;
          --lengthA;
          nofWinsB = 0;

          if (lengthA == 1) return CopyB();
          if (nofWinsA >= minGallop) break;
        }
      }

      ++minGallop;
      var firstIteration = true;
      while (nofWinsA >= kMinGallopWins || nofWinsB >= kMinGallopWins ||
             firstIteration) {
        firstIteration = false;

        minGallop = SmiMax(1, minGallop - 1);
        sortState.minGallop = minGallop;

        nofWinsA = GallopRight(
            tempArray, Identity(workArray[cursorB]),
            cursorTemp, lengthA, 0);

        if (nofWinsA > 0) {
          Copy(tempArray, cursorTemp, workArray, dest, nofWinsA);
          dest = dest + nofWinsA;
          cursorTemp = cursorTemp + nofWinsA;
          lengthA = lengthA - nofWinsA;

          if (lengthA == 1) return CopyB();

          if (lengthA == 0) return Succeed();
        }
        workArray[dest++] = workArray[cursorB++];
        if (--lengthB == 0) return Succeed();

        nofWinsB = GallopLeft(
            workArray, Identity(tempArray[cursorTemp]),
            cursorB, lengthB, 0);
        
        if (nofWinsB > 0) {
          Copy(workArray, cursorB, workArray, dest, nofWinsB);

          dest = dest + nofWinsB;
          cursorB = cursorB + nofWinsB;
          lengthB = lengthB - nofWinsB;

          if (lengthB == 0) return Succeed();
        }
        workArray[dest++] = tempArray[cursorTemp++];
        if (--lengthA == 1) return CopyB();
      }
      ++minGallop;  
      sortState.minGallop = minGallop;
    }
  } function Succeed() {
    if (lengthA > 0) {
      Copy(tempArray, cursorTemp, workArray, dest, lengthA);
    }
  } function CopyB() {

    Copy(workArray, cursorB, workArray, dest, lengthB);
    workArray[dest + lengthB] = tempArray[cursorTemp];
  }
}

function MergeHigh(
    baseA, lengthAArg, baseB, lengthBArg) {

  var lengthA = lengthAArg;
  var lengthB = lengthBArg;

  var workArray = sortState.workArray;
  var tempArray = GetTempArray(sortState, lengthB);
  Copy(workArray, baseB, tempArray, 0, lengthB);

  var dest = baseB + lengthB - 1;
  var cursorTemp = lengthB - 1;
  var cursorA = baseA + lengthA - 1;

  workArray[dest--] = workArray[cursorA--];

  {
    if (--lengthA == 0) return Succeed();
    if (lengthB == 1) return CopyA();

    var minGallop = sortState.minGallop;

    while (true) {
      var nofWinsA = 0;  
      var nofWinsB = 0;  

      while (true) {

        var order = sortState.Compare(
            Identity(tempArray[cursorTemp]),
            Identity(workArray[cursorA]));

        if (order < 0) {
          workArray[dest--] = workArray[cursorA--];

          ++nofWinsA;
          --lengthA;
          nofWinsB = 0;

          if (lengthA == 0) return Succeed();
          if (nofWinsA >= minGallop) break;
        } else {
          workArray[dest--] = tempArray[cursorTemp--];

          ++nofWinsB;
          --lengthB;
          nofWinsA = 0;

          if (lengthB == 1) return CopyA();
          if (nofWinsB >= minGallop) break;
        }
      }

      ++minGallop;
      var firstIteration = true;
      while (nofWinsA >= kMinGallopWins || nofWinsB >= kMinGallopWins ||
             firstIteration) {
        firstIteration = false;

        minGallop = SmiMax(1, minGallop - 1);
        sortState.minGallop = minGallop;

        var k = GallopRight(
            workArray, Identity(tempArray[cursorTemp]), baseA,
            lengthA, lengthA - 1);
        
        nofWinsA = lengthA - k;

        if (nofWinsA > 0) {
          dest = dest - nofWinsA;
          cursorA = cursorA - nofWinsA;
          Copy(workArray, cursorA + 1, workArray, dest + 1, nofWinsA);

          lengthA = lengthA - nofWinsA;
          if (lengthA == 0) return Succeed();
        }
        workArray[dest--] = tempArray[cursorTemp--];
        if (--lengthB == 1) return CopyA();

        k = GallopLeft(
            tempArray, Identity(workArray[cursorA]), 0,
            lengthB, lengthB - 1);
        
        nofWinsB = lengthB - k;

        if (nofWinsB > 0) {
          dest = dest - nofWinsB;
          cursorTemp = cursorTemp - nofWinsB;
          Copy(tempArray, cursorTemp + 1, workArray, dest + 1, nofWinsB);

          lengthB = lengthB - nofWinsB;
          if (lengthB == 1) return CopyA();

          if (lengthB == 0) return Succeed();
        }
        workArray[dest--] = workArray[cursorA--];
        if (--lengthA == 0) return Succeed();
      }
      ++minGallop;
      sortState.minGallop = minGallop;
    }
  } function Succeed() {
    if (lengthB > 0) {
      
      Copy(tempArray, 0, workArray, dest - (lengthB - 1), lengthB);
    }
  } function CopyA() {

    dest = dest - lengthA;
    cursorA = cursorA - lengthA;
    Copy(workArray, cursorA + 1, workArray, dest + 1, lengthA);
    workArray[dest] = tempArray[cursorTemp];
  }
}

function ComputeMinRunLength(nArg) {
  var n = nArg;
  var r = 0;  

  while (n >= 64) {
    r = r | (n & 1);
    n = n >> 1;
  }

  var minRunLength = n + r;
  
  return minRunLength;
}

function RunInvariantEstablished(
    pendingRuns, n) {
  if (n < 2) return true;

  var runLengthN = GetPendingRunLength(pendingRuns, n);
  var runLengthNM = GetPendingRunLength(pendingRuns, n - 1);
  var runLengthNMM = GetPendingRunLength(pendingRuns, n - 2);

  return runLengthNMM > runLengthNM + runLengthN;
}

function MergeCollapse(context, sortState) {
  var pendingRuns = sortState.pendingRuns;

  while (GetPendingRunsSize(sortState) > 1) {
    var n = GetPendingRunsSize(sortState) - 2;

    if (!RunInvariantEstablished(pendingRuns, n + 1) ||
        !RunInvariantEstablished(pendingRuns, n)) {
      if (GetPendingRunLength(pendingRuns, n - 1) <
          GetPendingRunLength(pendingRuns, n + 1)) {
        --n;
      }

      MergeAt(n);
    } else if (
        GetPendingRunLength(pendingRuns, n) <=
        GetPendingRunLength(pendingRuns, n + 1)) {
      MergeAt(n);
    } else {
      break;
    }
  }
}

function MergeForceCollapse(context, sortState) {
  var pendingRuns = sortState.pendingRuns;

  while (GetPendingRunsSize(sortState) > 1) {
    var n = GetPendingRunsSize(sortState) - 2;

    if (n > 0 &&
        GetPendingRunLength(pendingRuns, n - 1) <
            GetPendingRunLength(pendingRuns, n + 1)) {
      --n;
    }
    MergeAt(n);
  }
}

function ArrayTimSortImpl(context, sortState, length) {
  if (length < 2) return;
  var remaining = length;

  var low = 0;
  var minRunLength = ComputeMinRunLength(remaining);
  while (remaining != 0) {
    var currentRunLength = CountAndMakeRun(low, low + remaining);

    if (currentRunLength < minRunLength) {
      var forcedRunLength = SmiMin(minRunLength, remaining);
      BinaryInsertionSort(low, low + currentRunLength, low + forcedRunLength);
      currentRunLength = forcedRunLength;
    }

    PushRun(sortState, low, currentRunLength);

    MergeCollapse(context, sortState);

    low = low + currentRunLength;
    remaining = remaining - currentRunLength;
  }

  MergeForceCollapse(context, sortState);

}

  ArrayTimSortImpl(0,sortState,length);
  return workArray;
})
