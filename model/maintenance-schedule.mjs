/** A clock-only commitment made before the isolated new save is created. */
export function maintenanceSchedule(value = null) {
  if (value === null || value === undefined) return null;
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('Maintenance reload schedule must be an object');
  const time = x => Number.isFinite(x) && x >= 0;
  if (Object.keys(value).length === 1 && Array.isArray(value.atMs)) {
    if (value.atMs.some((x, i) => !time(x) || i > 0 && x <= value.atMs[i - 1])) throw new Error('Maintenance reload times must be finite, nonnegative and strictly increasing');
    return Object.freeze({ atMs: Object.freeze([...value.atMs]) });
  }
  if (Object.keys(value).length === 2 && time(value.firstMs) && Number.isFinite(value.everyMs) && value.everyMs > 0) {
    return Object.freeze({ firstMs: value.firstMs, everyMs: value.everyMs });
  }
  throw new Error('Maintenance reload schedule requires atMs, or firstMs and everyMs');
}

export function maintenanceRequestTime(schedule, index) {
  if (!schedule) return Infinity;
  return schedule.atMs ? schedule.atMs[index] ?? Infinity : schedule.firstMs + index * schedule.everyMs;
}
