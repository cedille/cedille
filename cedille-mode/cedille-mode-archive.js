const cedilleArchive = JSON.parse(document.getElementById('spans').innerHTML);
const cedilleData = document.getElementById('cedille-data');
const cedilleCode = document.getElementById('cedille-code-block');
const emptyNode = document.createTextNode("");

const removeClassFromSpans = (className, htmlSpans) => {
  htmlSpans.forEach(htmlSpan => htmlSpan.classList.remove(className));
};

const spanLength = ({ start, end }) => {
  return Math.abs(end - start);
};

const addEventListeners = (span, htmlSpan, htmlSpans) => {
  htmlSpan.addEventListener('click', () => {
    removeClassFromSpans('highlight', htmlSpans);
    htmlSpan.classList.add('highlight');
    displayData(span);
  }, { capture: true });

  htmlSpan.addEventListener('mouseover', () => {
    removeClassFromSpans('hover-highlight', htmlSpans);
    htmlSpan.classList.add('hover-highlight');
  }, { capture: true });

  htmlSpan.addEventListener('mouseout', () => {
    htmlSpan.classList.remove('hover-highlight');
  });
};

const createDiv = (className, textOrChildren) => {
  const node = document.createElement('div');
  node.className = className;

  if (typeof textOrChildren !== "object") {
    node.innerText = textOrChildren;
  } else {
    textOrChildren.forEach(child => node.appendChild(child));
  }

  return node;
};

const displayData = ({name, start, end, data}) => {
  const displayData = {
    name,
    start,
    end,
    ...data
  };

  cedilleData.innerHTML = null;
  Object.keys(displayData).forEach((key) => {
    const keyDiv = createDiv('cedille-key', key)
    const valueDiv = createDiv('cedille-value', displayData[key]);
    const bodyDiv = createDiv('cedille-pair', [keyDiv, valueDiv]);
    cedilleData.appendChild(bodyDiv);
  });
};

const displayCode = (filename) => {
  const { spans, text } = cedilleArchive[filename];
  const nodes = [null, ...text].map(c => document.createTextNode(c));
  const spansByAscendingLength = spans.sort((a, b) => spanLength(a) - spanLength(b));
  const htmlSpans = [];

  spansByAscendingLength.forEach(span => {
    const htmlSpan = document.createElement("span");
    htmlSpan.className = 'cedille-span';
    htmlSpans.push(htmlSpan);
    addEventListeners(span, htmlSpan, htmlSpans);

    for(let i = span.start; i < span.end; i++) {
      htmlSpan.appendChild(nodes[i] || emptyNode);
      nodes[i] = (i === span.start) ? htmlSpan : null;
    }
  });

  cedilleCode.innerHTML = null;
  cedilleCode.appendChild(nodes[1]);
};

const filename = Object.keys(cedilleArchive)[0];
displayCode(filename);
