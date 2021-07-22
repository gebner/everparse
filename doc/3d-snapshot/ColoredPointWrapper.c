#include "ColoredPointWrapper.h"
#include "EverParse.h"
#include "ColoredPoint.h"
void ColoredPointEverParseError(const char *StructName, const char *FieldName, const char *Reason);

typedef struct _ErrorFrame
{
	BOOLEAN filled;
	uint32_t start_pos;
	uint32_t end_pos;
	const char *typename;
	const char *fieldname;
	const char *reason;
} ErrorFrame;

void DefaultErrorHandler(
	const char *typename,
	const char *fieldname,
	const char *reason,
	uint8_t *context,
	uint32_t len,
	uint8_t *base,
	uint64_t start_pos,
	uint64_t end_pos)
{
	ErrorFrame *frame = (ErrorFrame*)context;
	if (!frame->filled)
	{
		frame->filled = TRUE;
		frame->start_pos = start_pos;
		frame->end_pos = end_pos;
		frame->typename = typename;
		frame->fieldname = fieldname;
		frame->reason = reason;
	}
}

BOOLEAN ColoredPointCheckColoredPoint1(uint8_t *base, uint32_t len) {
	ErrorFrame frame;
	frame.filled = FALSE;
	uint64_t result = ColoredPointValidateColoredPoint1( (uint8_t*)&frame, &DefaultErrorHandler, len, base, 0);
	if (EverParseResultIsError(result))
	{
		if (frame.filled)
		{
			ColoredPointEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ColoredPointCheckColoredPoint2(uint8_t *base, uint32_t len) {
	ErrorFrame frame;
	frame.filled = FALSE;
	uint64_t result = ColoredPointValidateColoredPoint2( (uint8_t*)&frame, &DefaultErrorHandler, len, base, 0);
	if (EverParseResultIsError(result))
	{
		if (frame.filled)
		{
			ColoredPointEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
