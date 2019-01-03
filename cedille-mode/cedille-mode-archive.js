
const cedilleSpans = JSON.parse(document.getElementById('spans').innerHTML);
const cedilleData = document.getElementById('cedille-data');
const htmlSpans = [...document.getElementsByClassName('cedille-span')];

function removeClassFromSpans(className) {
  htmlSpans.forEach(htmlSpan => htmlSpan.classList.remove(className));
}

function displayData({name, start, end, data}) {
  cedilleData.innerHTML = null;

  const displayData = {
    name,
    start,
    end,
    ...data
  };

  Object.keys(displayData).forEach((key) => {
    var bodyDiv = document.createElement('div');
    var keyDiv = document.createElement('div');
    var valueDiv = document.createElement('div');

    keyDiv.innerText = key;
    keyDiv.className = 'cedille-key';

    valueDiv.innerText = displayData[key];
    valueDiv.className = 'cedille-value';

    bodyDiv.className = 'cedille-pair';
    bodyDiv.appendChild(keyDiv);
    bodyDiv.appendChild(valueDiv);
    cedilleData.appendChild(bodyDiv);
  });
}

htmlSpans.forEach((htmlSpan, index) => {
  htmlSpan.addEventListener('click', () => {
    removeClassFromSpans('highlight');
    htmlSpan.classList.add('highlight');
    displayData(cedilleSpans[index]);
  }, { capture: true });

  htmlSpan.addEventListener('mouseover', () => {
    removeClassFromSpans('hover-highlight');
    htmlSpan.classList.add('hover-highlight');
  }, { capture: true });

  htmlSpan.addEventListener('mouseout', () => {
    htmlSpan.classList.remove('hover-highlight');
  });
});
