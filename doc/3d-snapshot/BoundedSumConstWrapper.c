#include "BoundedSumConstWrapper.h"
#include "EverParse.h"
#include "BoundedSumConst.h"
void BoundedSumConstEverParseError(char *x, char *y, char *z);
static char* BoundedSumConstStructNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "BoundedSum._boundedSum";
		case 2: return "BoundedSum._boundedSum";
		case 3: return "BoundedSum.mySum";
		case 4: return "Triangle._point";
		case 5: return "Triangle._point";
		case 6: return "OrderedPair._orderedPair";
		case 7: return "OrderedPair._orderedPair";
		case 8: return "HelloWorld._point";
		case 9: return "HelloWorld._point";
		case 10: return "ColoredPoint._point";
		case 11: return "ColoredPoint._point";
		case 12: return "ColoredPoint._coloredPoint1";
		case 13: return "ColoredPoint._coloredPoint2";
		case 14: return "Triangle2._point";
		case 15: return "Triangle2._point";
		case 16: return "Triangle2._triangle";
		case 17: return "Color._coloredPoint";
		case 18: return "Color._coloredPoint";
		case 19: return "Color._coloredPoint";
		case 20: return "ReadPair._Pair";
		case 21: return "ReadPair._Pair";
		case 22: return "BoundedSumWhere._boundedSum";
		case 23: return "BoundedSumWhere._boundedSum";
		case 24: return "BoundedSumWhere._boundedSum";
		case 25: return "GetFieldPtr._T";
		case 26: return "GetFieldPtr._T";
		case 27: return "BoundedSumConst._boundedSum";
		case 28: return "BoundedSumConst._boundedSum"; 
		default: return "";
	}
}

static char* BoundedSumConstFieldNameOfErr(uint64_t err) {
	switch (EverParseFieldIdOfResult(err)) {
		case 1: return "left";
		case 2: return "right";
		case 3: return "bound";
		case 4: return "x";
		case 5: return "y";
		case 6: return "lesser";
		case 7: return "greater";
		case 8: return "x";
		case 9: return "y";
		case 10: return "x";
		case 11: return "y";
		case 12: return "color";
		case 13: return "color";
		case 14: return "x";
		case 15: return "y";
		case 16: return "corners";
		case 17: return "col";
		case 18: return "x";
		case 19: return "y";
		case 20: return "first";
		case 21: return "second";
		case 22: return "__precondition";
		case 23: return "left";
		case 24: return "right";
		case 25: return "f1";
		case 26: return "f2";
		case 27: return "left";
		case 28: return "right"; 
		default: return "";
	}
}

BOOLEAN BoundedSumConstCheckBoundedSum(uint8_t *base, uint32_t len) {
	uint64_t result = BoundedSumConstValidateBoundedSum(len, base, 0);
	if (EverParseResultIsError(result)) {
		BoundedSumConstEverParseError(
	BoundedSumConstStructNameOfErr(result),
			BoundedSumConstFieldNameOfErr (result),
			EverParseErrorReasonOfResult(result));
		return FALSE;
	}
	return TRUE;
}
