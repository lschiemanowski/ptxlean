'use strict';
const search = document.querySelector('#search');
const status = document.querySelector('#status');
if (search && status) {
  const rows = Array.from(document.querySelectorAll('tbody tr[data-search]'));
  const filter = () => {
    const terms = search.value.toLowerCase().trim().split(/\s+/).filter(Boolean);
    let count = 0;
    for (const row of rows) {
      const matches = terms.every(term => row.dataset.search.includes(term));
      const selected = status.value === 'all' || row.dataset.status.split(' ').includes(status.value);
      row.hidden = !(matches && selected);
      if (!row.hidden) count++;
    }
    document.querySelector('#result-count').textContent = `${count} of ${rows.length} instruction entries`;
    document.querySelector('#empty').hidden = count !== 0;
  };
  search.addEventListener('input', filter);
  status.addEventListener('change', filter);
  filter();
}
