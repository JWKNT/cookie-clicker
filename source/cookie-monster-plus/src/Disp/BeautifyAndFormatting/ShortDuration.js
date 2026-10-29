/**
 * Formats a duration with its two most significant units (e.g. "3h 12m"), for compact displays
 * @param	{number}	seconds	Duration
 * @returns	{string}			Formatted duration
 */
export default function ShortDuration(seconds) {
  if (!Number.isFinite(seconds)) return '∞';
  let rest = Math.max(0, Math.ceil(seconds));
  const units = [
    ['y', 31536000],
    ['d', 86400],
    ['h', 3600],
    ['m', 60],
    ['s', 1],
  ];
  const parts = [];
  for (let i = 0; i < units.length && parts.length < 2; i++) {
    const amount = Math.floor(rest / units[i][1]);
    if (amount > 0 || (parts.length === 0 && i === units.length - 1)) {
      parts.push(`${amount}${units[i][0]}`);
      rest -= amount * units[i][1];
    } else if (parts.length > 0) break;
  }
  return parts.join(' ');
}
